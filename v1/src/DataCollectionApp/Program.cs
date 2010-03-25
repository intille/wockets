using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;
using System.Threading;
using System.IO;
using Wockets;
using Wockets.Utils;

namespace DataCollectionApp
{
    class Program
    {
        static Thread interfaceActivityThread;
        static Thread dataCollectionThread;
        static bool connecting = false;
        static WocketsController wc;
        /// <summary>
        /// This application is responsible for collecting data from the wockets, timestamping it and saving it
        /// It can run in 2 modes: - shared memory mode that allows multiple applications to access its buffers
        /// or - local memory mode that allocates memory within the applications address space
        /// </summary>
        /// <param name="args"></param>
        static void Main(string[] args)
        {
            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();
            string firstCard = "";
            //iterate through them
            for (int x = 0; x < fsi.Length; x++)
            {
                //check to see if this is a temporary storage card (e.g. SD card)
                if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                {
                    firstCard = fsi[x].FullName;
                    try
                    {
                        Directory.CreateDirectory(firstCard + "\\writable");
                        Directory.Delete(firstCard + "\\writable");
                    }
                    catch (Exception)
                    {
                        firstCard = "";
                        continue;
                    }
                    //if so, return the path

                    break;
                }
            }

            string storageDirectory = firstCard + "\\Wockets\\Session" + DateTime.Now.Month + "-" + DateTime.Now.Day + "-" + DateTime.Now.Hour + "-" + DateTime.Now.Minute + "-" + DateTime.Now.Second;
            connecting = true;
            Logger.InitLogger(storageDirectory);
            wc = new WocketsController("", "", "");
            wc._storageDirectory = storageDirectory;
            wc.FromXML("\\Program Files\\wockets\\NeededFiles\\SensorConfigurations\\SensorDataFahd.xml");
            for (int i = 0; (i < wc._Sensors.Count); i++)
                wc._Sensors[i]._RootStorageDirectory = storageDirectory + "\\data\\raw\\PLFormat\\"; 
            wc.Initialize();
            //default is local memory
            interfaceActivityThread = new Thread(new ThreadStart(InterfaceActivityTracker));
            dataCollectionThread = new Thread(new ThreadStart(DataCollection));
            interfaceActivityThread.Start();
            dataCollectionThread.Start();
            dataCollectionThread.Join();

        }

        static void InterfaceActivityTracker()
        {

            while (true)
            {
                if (connecting)
                {
                    SystemIdleTimerReset();
                    if ((wc != null) && (wc._Sensors.Count>0))
                    {
                        bool dataReceived = true;
                        for (int i = 0; (i < wc._Sensors.Count); i++)
                            if (wc._Sensors[i].SavedPackets != 2400)
                                dataReceived = false;
                        if (dataReceived)
                        {
                            connecting = false;
                            wc.Pause();
                            for (int i = 0; (i < wc._Sensors.Count); i++)
                            {
                                //wc._Sensors[i].Save();
                                wc._Sensors[i].SavedPackets = 0;
                                wc._Receivers[i]._Status = Wockets.Receivers.ReceiverStatus.Disconnected;
                            }
                            //wc.Dispose();           
                        }
                    }
                }

                Thread.Sleep(1000);
            }
        }


        [StructLayout(LayoutKind.Sequential)]
        public struct SYSTEMTIME
        {
            [MarshalAs(UnmanagedType.U2)]
            public short Year;
            [MarshalAs(UnmanagedType.U2)]
            public short Month;
            [MarshalAs(UnmanagedType.U2)]
            public short DayOfWeek;
            [MarshalAs(UnmanagedType.U2)]
            public short Day;
            [MarshalAs(UnmanagedType.U2)]
            public short Hour;
            [MarshalAs(UnmanagedType.U2)]
            public short Minute;
            [MarshalAs(UnmanagedType.U2)]
            public short Second;
            [MarshalAs(UnmanagedType.U2)]
            public short Milliseconds;

            public SYSTEMTIME(DateTime dt)
            {
                //dt = dt.ToUniversalTime();  // SetSystemTime expects the SYSTEMTIME in UTC
                Year = (short)dt.Year;
                Month = (short)dt.Month;
                DayOfWeek = (short)dt.DayOfWeek;
                Day = (short)dt.Day;
                Hour = (short)dt.Hour;
                Minute = (short)dt.Minute;
                Second = (short)dt.Second;
                Milliseconds = (short)dt.Millisecond;
            }
        }

        public class CE_NOTIFICATION_TRIGGER
        {

            public UInt32 Size = 0;
            public UInt32 Type = 1;
            public UInt32 Event = 11;
            [MarshalAs(UnmanagedType.LPWStr)]
            public string pAppName;
            [MarshalAs(UnmanagedType.LPWStr)]
            public string pArgs;
            public SYSTEMTIME StartTime;
            public SYSTEMTIME EndTime;
        }

        public class CE_USER_NOTIFICATION
        {
            public UInt32 ActionFlags;
            [MarshalAs(UnmanagedType.LPWStr)]
            public string pDialogTitle;
            [MarshalAs(UnmanagedType.LPWStr)]
            public string DialogText;
            [MarshalAs(UnmanagedType.LPWStr)]
            public string Sound;
            public UInt32 MaxSound;
            public UInt32 Reserved;
        }
        [DllImport("coredll.dll", EntryPoint = "CeClearUserNotification", SetLastError = true)]
        private static extern bool CeClearUserNotification(int hNotification);

        [DllImport("coredll.dll", EntryPoint = "CeSetUserNotificationEx", SetLastError = true)]
        private static extern int CeSetUserNotificationEx(int hNotification, byte[] lpTrigger, byte[] lpUserNotification);

        [DllImport("coredll.dll")]
        private static extern IntPtr CeSetUserNotificationEx(IntPtr notification, CE_NOTIFICATION_TRIGGER notificationTrigger, CE_USER_NOTIFICATION userNotification);
        [DllImport("CoreDll.dll")]
        public static extern void SystemIdleTimerReset();

        static void DataCollection()
        {
            NamedEvents namedEvent = new NamedEvents();
            NamedEvents waitDisconnectEvent = new NamedEvents();

            int k = 0;

            //wc.InitAgain();
            while (true)
            {
         
                //on receive a disconnect, insert an event and wakeup after 1 minute
                string appName = "\\\\.\\Notifications\\NamedEvents\\MyTestEvent" + k;
                string args = "";

                System.DateTime dt = System.DateTime.Now.AddSeconds(60);
                CE_NOTIFICATION_TRIGGER notificationTrigger = new CE_NOTIFICATION_TRIGGER();
                notificationTrigger.Type = 2;
                notificationTrigger.pAppName = appName;
                notificationTrigger.pArgs = args;
                notificationTrigger.StartTime = new SYSTEMTIME(dt);
                notificationTrigger.EndTime = new SYSTEMTIME();
                notificationTrigger.Size = (UInt32)Marshal.SizeOf(notificationTrigger); // This line needs the compile switch /unsafe
                IntPtr notificationHandle = CeSetUserNotificationEx(IntPtr.Zero, notificationTrigger, null);


                namedEvent.Receive("MyTestEvent" + k);                
                connecting = true;
                wc.Unpause();
   

                //on wakeup, attempt to reconnect
                //connect to the wocket
                //save the data


                //PowerPolicyNotify(PPNMessage.PPN_UNATTENDEDMODE, -1);               
                TextWriter tw = new StreamWriter("test.csv", true);
                SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                tw.WriteLine(++k + "," + DateTime.Now.ToLongTimeString() + "," + bpower.BatteryLifePercent + "," + bpower.BatteryVoltage + "," + bpower.BatteryCurrent + "," + bpower.BatteryTemperature);
                tw.Close();


                namedEvent.Reset();
                CeClearUserNotification((int)notificationHandle);
                //wc.InitAgain();               
            }
        }
    }
}
