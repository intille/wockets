using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;
using System.Threading;
using System.IO;
using Wockets;
using Wockets.Utils;
using Wockets.Utils.IPC;
using Wockets.Utils.network;
using Wockets.Data.Configuration;
using Wockets.Decoders.Accelerometers;
using Wockets.Utils.IPC.Queues;
using Wockets.Receivers;
using Microsoft.Win32;

namespace DataCollectionApp
{
    class Program
    {
        static Thread interfaceActivityThread;
        static Thread dataCollectionThread;
        static Thread terminationThread;
        static bool connecting = false;
        static WocketsController wc;
        static int secondsToConnect = 0;
        static bool[] countSeconds = null;
        /// <summary>
        /// This application is responsible for collecting data from the wockets, timestamping it and saving it
        /// It can run in 2 modes: - shared memory mode that allows multiple applications to access its buffers
        /// or - local memory mode that allocates memory within the applications address space
        /// </summary>
        /// <param name="args"></param>
        static void Main(string[] args)
        {

           /* RegistryKey rk = Registry.LocalMachine.OpenSubKey("System\\CurrentControlSet\\Control\\Power\\State\\Suspend", true);
            rk.SetValue("wav1:", 0, RegistryValueKind.DWord);
            rk.Close();*/

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
            /*
            try
            {
                Directory.Delete(firstCard + "\\Wockets");
            }
            catch
            {
            }

            try
            {               
                File.Delete("test.csv");
            }
            catch
            {
            }
            */
     
            string storageDirectory = firstCard + "\\Wockets\\Session" + DateTime.Now.Month + "-" + DateTime.Now.Day + "-" + DateTime.Now.Hour + "-" + DateTime.Now.Minute + "-" + DateTime.Now.Second;           
            connecting = true;
            Logger.InitLogger(storageDirectory);

            WocketsConfiguration configuration = new WocketsConfiguration();
            configuration.FromXML("\\Program Files\\wockets\\NeededFiles\\Master\\Configuration.xml");
            CurrentWockets._Configuration = configuration;            
            wc = new WocketsController("", "", "");
            CurrentWockets._Controller = wc;
            wc._storageDirectory = storageDirectory;
            wc.FromXML("\\Program Files\\wockets\\NeededFiles\\SensorConfigurations\\SensorDataFahd.xml");
            if (!File.Exists("test.csv"))
            {

                TextWriter tw = new StreamWriter("test.csv", true);
                tw.WriteLine("Index,");
                tw.Close();
            }
            countSeconds = new bool[wc._Sensors.Count];
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                wc._Sensors[i]._Loaded = true;
                wc._Sensors[i]._Flush = true;
                wc._Sensors[i]._RootStorageDirectory = storageDirectory + "\\data\\raw\\PLFormat\\";
                countSeconds[i] = false;
            }
            wc._Bursty = true;
            wc.Initialize();
            //default is local memory
            interfaceActivityThread = new Thread(new ThreadStart(InterfaceActivityTracker));
            interfaceActivityThread.Priority = ThreadPriority.Highest;
            dataCollectionThread = new Thread(new ThreadStart(DataCollection));
            terminationThread = new Thread(new ThreadStart(TerminateWockets));
            terminationThread.Start();
            interfaceActivityThread.Start();
            dataCollectionThread.Start();


            activitySignal = OpenEvent(EVENT_ALL_ACCESS, false, ActiveName);
            if (activitySignal == IntPtr.Zero)
            {
                // Can't open the events -- this device probably doesn't define them
                return;
            }
            activityListenerThread = new Thread(activityListener);
            activityListenerThread.Start();
            dataCollectionThread.Join();

        }
        static void TerminateWockets()
        {
            NamedEvents namedEvent = new NamedEvents();
            namedEvent.Receive("TerminateWockets");
            System.Diagnostics.Process.GetCurrentProcess().Kill();
        }

        private static int EVENT_ALL_ACCESS = 0x1F0003;
        private static String ActiveName = "PowerManager/UserActivity_Active";
        private static IntPtr activitySignal;
        private static Thread activityListenerThread;
        [DllImport("coredll.dll")]
        private static extern IntPtr OpenEvent(int desiredAccess, bool inheritHandle, string name);

        [DllImport("coredll.dll")]
        private static extern int WaitForSingleObject(IntPtr handle, int milliseconds);
        private static DateTime lastActivity = DateTime.Now;
        private static void activityListener()
        {
            while (true)
            {
                // waiting for activity signal, will block the thread, works globally.
                WaitForSingleObject(activitySignal, int.MaxValue);    
                lastActivity = DateTime.Now;
                Thread.Sleep(5000);
            }
        }

        static void InterfaceActivityTracker()
        {

            int k = 0;
            P2PMessageQueue mQue = new P2PMessageQueue(false,"WocketStatistics");
            int expectedPackets = 0;
            int[] dataSavedSeconds = new int[wc._Sensors.Count];
            
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                dataSavedSeconds[i] = 0;

            }
            while (true)
            {
                if (connecting)
                {
                    SystemIdleTimerReset();
                    if ((wc != null) && (wc._Sensors.Count > 0))
                    {
                        //Check 2 things, num of connection failures
                        // check if data received is > 0
                        // if num connections >2, ready to pause
                        // if data received is >0, ready to pause within 2 seconds.


                        
                        bool receivedSomeData = true;
                        bool receivedFullData = true;
                        for (int i = 0; (i < wc._Sensors.Count); i++)
                        {
                            //halt, if either 1 successful connection was made
                            // or any data was received
                            // or 3 or more reconnections were made
                            if ((((RFCOMMReceiver)wc._Receivers[i])._SuccessfulConnections == 0) &&
                                (wc._Sensors[i]._ReceivedPackets == 0) &&
                                (((RFCOMMReceiver)wc._Receivers[i])._Reconnections <= 3))
                            {
                                receivedSomeData = false;
                                break;
                            }
                            else
                                receivedFullData &= (wc._Sensors[i]._ReceivedPackets == ((WocketsDecoder)wc._Decoders[i])._ExpectedPacketCount);
                        }

                        if (receivedSomeData)
                        {
                            // if didnt get full data, sleep for 2 seconds
                            if (!receivedFullData)
                                Thread.Sleep(3000);

                            //save whatever we have so far then sleep
                            connecting = false;
                            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                            string log_line = ++k + "," + DateTime.Now.ToLongTimeString() + "," + bpower.BatteryLifePercent + "," + bpower.BatteryVoltage + "," + bpower.BatteryCurrent + "," + bpower.BatteryTemperature;

                            for (int i = 0; (i < wc._Sensors.Count); i++)
                            {
                                log_line += "," + wc._Sensors[i]._ReceivedPackets + "," + ((RFCOMMReceiver)wc._Receivers[i])._SuccessfulConnections + "," + ((RFCOMMReceiver)wc._Receivers[i])._Reconnections + "," + ((RFCOMMReceiver)wc._Receivers[i])._ConnectionTime
                                dataSavedSeconds[i] = 0;
                                countSeconds[i] = false;
                                ((WocketsDecoder)wc._Decoders[i])._ExpectedPacketCount = 0;
                            }

                            wc._Polling = false;

                            //shutting down BT here causes a strange delay on wakeup.
                            while (true)
                            {
                                try
                                {
                                    if (Wockets.Utils.network.NetworkStacks._BluetoothStack.Dispose())
                                        break;
                                }
                                catch
                                {
                                }
                                SystemIdleTimerReset();
                                Thread.Sleep(1000);
                            }

                            TextWriter tw = new StreamWriter("test.csv", true);
                            tw.WriteLine(log_line);
                            tw.Close();

                            try
                            {
                                mQue.Send(new Message(System.Text.Encoding.ASCII.GetBytes(log_line), false));
                            }
                            catch
                            {
                            }

                            SystemIdleTimerReset();
                            for (int i = 0; (i < wc._Sensors.Count); i++)
                                wc._Sensors[i].Save();



                            Thread.Sleep(1000);
                            if (DateTime.Now.Subtract(lastActivity).TotalSeconds > 30)
                                SetSystemPowerState(null, POWER_STATE_SUSPEND, POWER_FORCE);
                         
                        }



                        /*bool dataReceived = true;
                        for (int i = 0; (i < wc._Sensors.Count); i++)
                        {
                          
                            if ((wc._Sensors[i]._ReceivedPackets ==0) || (wc._Sensors[i]._ReceivedPackets < ((WocketsDecoder)wc._Decoders[i])._ExpectedPacketCount))
                                dataReceived = false;

                            // if connected once start counting seconds   
                            if (wc._Receivers[i]._Status == Wockets.Receivers.ReceiverStatus.Connected)
                                countSeconds[i] = true;

                            if (countSeconds[i])       
                                dataSavedSeconds[i] = dataSavedSeconds[i] + 1;                            
                            
                        }
                        bool timeoutexpired = true;
                        for (int i = 0; (i < wc._Sensors.Count); i++)
                            if (dataSavedSeconds[i] < 20)
                                timeoutexpired = false;
                        if ((dataReceived) || (timeoutexpired))
                        {

                            connecting = false;
                            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                            string log_line = ++k + "," + DateTime.Now.ToLongTimeString() + "," + bpower.BatteryLifePercent + "," + bpower.BatteryVoltage + "," + bpower.BatteryCurrent + "," + bpower.BatteryTemperature;

                            for (int i = 0; (i < wc._Sensors.Count); i++)
                            {
                                log_line += "," + wc._Sensors[i]._ReceivedPackets + "," + ((WocketsDecoder)wc._Decoders[i])._ExpectedPacketCount;
                                dataSavedSeconds[i] = 0;
                                countSeconds[i] = false;
                                ((WocketsDecoder)wc._Decoders[i])._ExpectedPacketCount = 0;                          
                            } 

                            wc._Polling = false;
             
                            //shutting down BT here causes a strange delay on wakeup.
                            while (true)
                            {
                                try
                                {
                                    if (Wockets.Utils.network.NetworkStacks._BluetoothStack.Dispose())
                                        break;
                                }
                                catch
                                {
                                }
                                SystemIdleTimerReset();
                                Thread.Sleep(1000);
                            }
                                                                                                             
                            TextWriter tw = new StreamWriter("test.csv", true);
                            tw.WriteLine(log_line);
                            tw.Close();
                            
                            try
                            {                             
                                mQue.Send(new Message(System.Text.Encoding.ASCII.GetBytes(log_line), false));
                            }
                            catch
                            {
                            }

                            SystemIdleTimerReset();
                             for (int i = 0; (i < wc._Sensors.Count); i++)
                                wc._Sensors[i].Save();

                        
                       
                            Thread.Sleep(1000);
                            if (DateTime.Now.Subtract(lastActivity).TotalSeconds > 30)
                               SetSystemPowerState(null, POWER_STATE_SUSPEND, POWER_FORCE);
                         
                        }*/
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

        [DllImport("coredll.dll", SetLastError = true)]
        static extern int SetSystemPowerState(string psState, int StateFlags, int Options);


        const int POWER_STATE_ON = 0x00010000;
        const int POWER_STATE_OFF = 0x00020000;
        const int POWER_STATE_IDLE = 0x00100000;
        const int POWER_STATE_SUSPEND = 0x00200000;
        const int POWER_FORCE = 4096;
        const int POWER_STATE_RESET = 0x00800000;

        public enum PPNMessage
        {
            PPN_REEVALUATESTATE = 1,
            PPN_POWERCHANGE = 2,
            PPN_UNATTENDEDMODE = 3,
            PPN_SUSPENDKEYPRESSED = 4,
            PPN_POWERBUTTONPRESSED = 4,
            PPN_SUSPENDKEYRELEASED = 5,
            PPN_APPBUTTONPRESSED = 6,

        }

        [DllImport("CoreDLL")]
        public static extern int PowerPolicyNotify(
          PPNMessage dwMessage,
            int option
            //    DevicePowerFlags);
        );
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
                SystemIdleTimerReset();
                try
                {
                    Wockets.Utils.network.NetworkStacks._BluetoothStack.Initialize();
                }
                catch
                {
                }
                Thread.Sleep(3000);
                //PowerPolicyNotify(PPNMessage.PPN_UNATTENDEDMODE, -1);               
                //SetSystemPowerState(null,POWER_STATE_ON, POWER_FORCE);
                for (int i = 0; (i < wc._Sensors.Count); i++)           
                    countSeconds[i] = true;
                connecting = true;
                //wc.Unpause();
                wc._Polling = true;

                k++;
                //on wakeup, attempt to reconnect
                //connect to the wocket
                //save the data


                
              


                namedEvent.Reset();
                CeClearUserNotification((int)notificationHandle);
                //wc.InitAgain();               
            }
        }
    }
}
