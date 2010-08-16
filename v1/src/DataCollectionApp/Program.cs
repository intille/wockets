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
using Wockets.Utils.sms;
using InTheHand.Net.Bluetooth;
using Wockets.Data.Types;

namespace DataCollectionApp
{
    class Program
    {
        static Thread interfaceActivityThread;
        static Thread dataCollectionThread;
        static Thread terminationThread;
        static bool connecting = false;
        static WocketsController wc;
        static bool[] countSeconds = null;
        static SMSManager smsMgr;
        
        static String gatewayNumber = "6173012490";
        static char projectCode = 'W';
        static char programCode = '1';

        static int reminderID = 0;
        static DateTime reminderDateTime;

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
            smsMgr = new SMSManager(programCode, programCode);

            DateTime now = DateTime.Now;
            string storageDirectory = firstCard + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") +"-"+ now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");           
            connecting = true;
            Logger.InitLogger(storageDirectory+"\\log\\");

            WocketsConfiguration configuration = new WocketsConfiguration();
            configuration.FromXML("\\Program Files\\wockets\\NeededFiles\\Master\\Configuration.xml");
            try
            {
                File.Copy("\\Program Files\\wockets\\NeededFiles\\Master\\Configuration.xml", storageDirectory + "\\Configuration.xml");
            }
            catch
            { 
            }
            CurrentWockets._Configuration = configuration;            
            wc = new WocketsController("", "", "");
            CurrentWockets._Controller = wc;
            wc._storageDirectory = storageDirectory;
            wc.FromXML("\\Program Files\\wockets\\NeededFiles\\SensorConfigurations\\SensorDataFahd.xml");
            try
            {
                File.Copy("\\Program Files\\wockets\\NeededFiles\\SensorConfigurations\\SensorDataFahd.xml", storageDirectory + "\\SensorData.xml");
            }
            catch
            {
            }

            wc._Mode = MemoryMode.BluetoothToLocal;
            for (int i = 0; (i < wc._Receivers.Count); i++)
                if (BluetoothSecurity.SetPin(new InTheHand.Net.BluetoothAddress(((Wockets.Receivers.RFCOMMReceiver)wc._Receivers[i])._AddressBytes), "1234"))
                    Console.Write("Success");
                else
                    Console.Write("Failure");
            if (!File.Exists("test.csv"))
            {

                TextWriter tw = new StreamWriter("test.csv", true);
                tw.Write("Index, Time, Battery %, Voltage, Current, Temperature");
                for (int i = 0; (i < wc._Sensors.Count); i++)
                {
                    tw.Write(", Received Packets "+i+", Expected Packet Count"+i+",Num Succ Connections "+i+",Num Reconnections "+i+", Connection Time "+i);
                }
                tw.WriteLine();
                tw.Close();
            }

            if (!File.Exists("testsummary.csv"))
            {

               
                for (int i = 0; (i < wc._Sensors.Count); i++)
                {
                    TextWriter tw1 = new StreamWriter("testsummary"+i+".csv", true);
                    tw1.Write("Index, Time,Summary");
                    tw1.WriteLine();
                    tw1.Close();
                }
                
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
            wc._TMode = TransmissionMode.Bursty60;
            wc.Initialize();
            reminderDateTime = DateTime.Now.AddSeconds(60);
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
                            if ((((RFCOMMReceiver)wc._Receivers[i])._SuccessfulConnections <= 1) &&
                                (wc._Sensors[i]._ReceivedPackets == 0) &&
                                (((RFCOMMReceiver)wc._Receivers[i])._Reconnections <= 3))
                            {
                                receivedSomeData = false;
                                break;
                            }
                            else
                                receivedFullData &= (wc._Sensors[i]._ReceivedPackets == ((WocketsDecoder)wc._Decoders[i])._ExpectedBatchCount);
                        }

                        if (receivedSomeData)
                        {
                            // if didnt get full data, sleep for 2 seconds
                            if (!receivedFullData)
                                Thread.Sleep(3000);

                            //save whatever we have so far then sleep
                            connecting = false;
                            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                            DateTime now=DateTime.Now;
                            double unixtime = WocketsTimer.GetUnixTime(now);
                            string currentTime = now.ToString("yyyy-MM-dd HH:mm:ss");
                            string log_line = ++k + "," + currentTime + "," + bpower.BatteryLifePercent + "," + bpower.BatteryVoltage + "," + bpower.BatteryCurrent + "," + bpower.BatteryTemperature;


                            for (int i = 0; (i < wc._Sensors.Count); i++)
                            {
                                /* string smslog = i + "," + currentTime + "," + WocketsTimer.GetUnixTime() + ",-5,wtm,WocketsController," + ((WocketsDecoder)wc._Decoders[i])._ExpectedBatchCount + ":" + wc._Sensors[i]._ReceivedPackets + ":" + bpower.BatteryLifePercent;
                                 try
                                 {
                                     SMSManager.SMSErrorMessage errorMsg = smsMgr.sendControlledSMS(gatewayNumber, projectCode, programCode, "txt", smslog, false);
                                     if (errorMsg != SMSManager.SMSErrorMessage.None)
                                     {
                                     }
                                 }
                                 catch (Exception e)
                                 {
                                 }*/

                                log_line += "," + wc._Sensors[i]._ReceivedPackets + "," + ((WocketsDecoder)wc._Decoders[i])._ExpectedBatchCount + "," + ((RFCOMMReceiver)wc._Receivers[i])._SuccessfulConnections + "," + ((RFCOMMReceiver)wc._Receivers[i])._Reconnections + "," + ((RFCOMMReceiver)wc._Receivers[i])._ConnectionTime;
                                dataSavedSeconds[i] = 0;
                                countSeconds[i] = false;
                                ((WocketsDecoder)wc._Decoders[i])._ExpectedBatchCount = 0;

                                TextWriter tw2 = new StreamWriter("testsummary" + i + ".csv", true);
                                for (int j = 0; (j < ((WocketsDecoder)wc._Decoders[i])._ActivityCountIndex); j++)
                                    tw2.WriteLine(k + "," + currentTime + ","+((WocketsDecoder)wc._Decoders[i])._ActivityCounts[j]);                                
                                ((WocketsDecoder)wc._Decoders[i])._ActivityCountIndex = 0;
                                tw2.Close();
                            }
                           

                            /*string activitylog = "1," + currentTime + "," + unixtime + ",-5,aat,SystemAnnotater," + ((long)WocketsTimer.GetUnixTime(now.AddSeconds(-60.0))).ToString() + ":" + ((long)unixtime).ToString() + ":" + "Active";
                            try
                            {
                                SMSManager.SMSErrorMessage errorMsg = smsMgr.sendControlledSMS(gatewayNumber, projectCode, programCode, "txt", activitylog, false);
                                if (errorMsg != SMSManager.SMSErrorMessage.None)
                                {
                                }
                            }
                            catch
                            {
                            }*/
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
        );
        static void DataCollection()
        {
            NamedEvents namedEvent = new NamedEvents();
            NamedEvents waitDisconnectEvent = new NamedEvents();

            while (true)
            {

                //on receive a disconnect, insert an event and wakeup after 1 minute
                string appName = "\\\\.\\Notifications\\NamedEvents\\WocketsEvent" + reminderID;
                string args = "";

                CE_NOTIFICATION_TRIGGER notificationTrigger = new CE_NOTIFICATION_TRIGGER();
                notificationTrigger.Type = 2;
                notificationTrigger.pAppName = appName;
                notificationTrigger.pArgs = args;
                notificationTrigger.StartTime = new SYSTEMTIME(reminderDateTime);
                notificationTrigger.EndTime = new SYSTEMTIME();
                notificationTrigger.Size = (UInt32)Marshal.SizeOf(notificationTrigger); // This line needs the compile switch /unsafe
                IntPtr notificationHandle = CeSetUserNotificationEx(IntPtr.Zero, notificationTrigger, null);
                reminderDateTime = reminderDateTime.AddSeconds(60);

                namedEvent.Receive("WocketsEvent" + reminderID++);
                SystemIdleTimerReset();
                try
                {
                    Wockets.Utils.network.NetworkStacks._BluetoothStack.Initialize();
                }
                catch
                {
                }
                Thread.Sleep(3000);
                for (int i = 0; (i < wc._Sensors.Count); i++)           
                    countSeconds[i] = true;
                connecting = true;                
                wc._Polling = true;
              

                              
                namedEvent.Reset();
                CeClearUserNotification((int)notificationHandle);             
            }
        }
    }
}
