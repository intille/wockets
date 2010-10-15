using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Xml;
using System.Threading;
using Wockets;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Sensors;
using Wockets.Utils;
using Wockets.Utils.network;
using Wockets.Data.Commands;
using Wockets.Data.Accelerometers;
using Wockets.Data.Annotation;
using Wockets.Data.Features;
using Wockets.Data.Types;
using Wockets.Decoders.Accelerometers;
using WocketsWeka;
using weka.classifiers;
using weka;
using weka.core;
using weka.classifiers.trees;
using Wockets.Utils.IPC;
using System.Runtime.InteropServices;
#if (PocketPC)
using Wockets.Utils.IPC.MMF;
using Wockets.Kernel;
#endif

namespace Wockets
{
    /// <summary>
    /// The wockets controller manages data connections, writes raw data and classifies data
    /// </summary>
    public sealed class WocketsController : XMLSerializable
    {                
        #region Serialization Constants
        private const string SENSORDATA_ELEMENT = "SENSORDATA";
        #endregion Serialization Constants

        #region Wockets Controller Information
        public string _Description;
        public string _Filename;
        public string _Name;
        #endregion Wockets Controller Information

        #region Wockets controller components
        public ReceiverList _Receivers;
        public DecoderList _Decoders;        
        public SensorList _Sensors;
        #endregion Wockets controller components

        #region Threads instantiated by the controller
        
        /// <summary>
        /// Polls the data from BT serial to a local buffer, a shared memory buffer or polls data
        /// from a shared memory buffer to a local buffer.
        /// </summary>
        private Thread aPollingThread;

        /// <summary>
        /// Saves data
        /// </summary>
        private Thread aSavingThread;

        /// <summary>
        /// Handle to the classification thread
        /// </summary>
        private Thread aClassifyingThread;


        #endregion Threads instantiated by the controller


        public int extractedVectors = 0;
        private int structureFileExamples = 0;
        private AutoResetEvent waitToPollEvent;
        private AutoResetEvent pollingEvent;
        private bool polling = true;
        private AutoResetEvent savingEvent;
        private AutoResetEvent waitToSaveEvent;
        private bool saving = true;
        private AutoResetEvent classifyingEvent;
        private bool classifying = false;        
        private AutoResetEvent trainingEvent;
        private bool training = false;        
        private TextWriter trainingTW = null;
        private TextWriter structureTW = null;
        private Instances instances;        
        private Classifier classifier;
        public string _StorageDirectory;
        private Session annotatedSession;        
        public double StartTime = 0;
        /// <summary>
        /// Stores the current record that is being annotated
        /// </summary>
        //private AnnotatedRecord currentRecord;
        public Annotation currentRecord;

           
        

        public MemoryMode _Mode = MemoryMode.BluetoothToLocal;
        public TransmissionMode _TMode = TransmissionMode.Continuous;

        /// <summary>
        /// A property that controls the data saving thread. When set to true the saving thread is signaled to run.
        /// When set to false it is guruanteed that the saving thread will be stopped prior to the call returning to avoid race
        /// conditions
        /// </summary>
        public bool _Saving
        {
            get
            {
                return this.saving;
            }
            set
            {
                this.saving = value;
                // if saving is true then wakeup the saving thread
                if (value)
                    this.savingEvent.Set();
                else //if saving is false then block until saving is done.
                    this.waitToSaveEvent.WaitOne();                                
            }
        }

        public bool _Polling
        {
            get
            {
                return this.polling;
            }
            set
            {               
                this.polling = value;
                if (value)
                    this.pollingEvent.Set();
                else
                    this.waitToPollEvent.WaitOne();                
            }
        }



        public bool _Training
        {
            get
            {
                return this.training;
            }
            set
            {
                if (value)
                    this.trainingEvent.Set();
                this.training = value;
            }
        }

        public bool _Classifying
        {
            get
            {
                return this.classifying;
            }
            set
            {
                if (value)
                    this.classifyingEvent.Set();
                this.classifying = value;
            }
        }



        public WocketsController(string name, string filename, string description)
        {

            this._Name = name;
            this._Filename = filename;
            this._Description = description;



            
            this.savingEvent = new AutoResetEvent(false);
            this.waitToSaveEvent = new AutoResetEvent(false);

            this.pollingEvent = new AutoResetEvent(false);
            this.waitToPollEvent = new AutoResetEvent(false);
            this.classifyingEvent = new AutoResetEvent(false);
            this.trainingEvent = new AutoResetEvent(false);

            this._Decoders = new DecoderList();
            this._Receivers = new ReceiverList();
            this._Sensors = new SensorList();
                     
        }


        public void Deinitialize()
        {
            if (aPollingThread!=null)
                aPollingThread.Abort();

            if (aSavingThread!=null)
                aSavingThread.Abort();

            for (int i = 0; (i < this._Receivers.Count); i++)
            {
                this._Receivers[i].Dispose();
                this._Decoders[i].Dispose();
                this._Sensors[i].Dispose();
            }

            try
            {
                Wockets.Utils.network.NetworkStacks._BluetoothStack.Dispose();                    
            }
            catch
            {
            }
        }
        public void Initialize()
        {


            if (this._Mode == MemoryMode.SharedToLocal)
            {
                for (int i = 0; (i < this._Decoders.Count); i++)
                {
                    try
                    {
                        this._Decoders[i].Initialize();
                    }
                    catch (Exception e)
                    {
                    }
                }
            }
            else if (this._Mode != MemoryMode.SharedToLocal)
            {

                for (int i = 0; (i < this._Receivers.Count); i++)
                {
                    try
                    {
                        if (this._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                            ((RFCOMMReceiver)this._Receivers[i])._TMode = this._TMode;   
                        if (this._Sensors[i]._Loaded)
                        {
                            //Only initialize receiver if continuous
                            if (this._TMode== TransmissionMode.Continuous)
                                this._Receivers[i].Initialize();

                            this._Decoders[i].Initialize();
                        }               
                    }
                    catch (Exception e)
                    {
                    }

                }
            }
            
            classifying = true;
            
            //Priorities are very critical to avoid buffer overflow                      
            if (this._TMode == TransmissionMode.Continuous)
                this.polling = true;
            else
                this.polling = false;
            
            aPollingThread = new Thread(new ThreadStart(Poll));
            aPollingThread.Priority = ThreadPriority.Highest;            
            aPollingThread.Start();


            // Save only if the wocket controller is the kernel: Bluetooth to shared or
            // if it is in an application address space BluetoothToLocal
            if (this._TMode == TransmissionMode.Continuous)
            {
                if ((this._Mode == MemoryMode.BluetoothToShared) || (this._Mode == MemoryMode.BluetoothToLocal))
                {
                    _Saving = true;
                    aSavingThread = new Thread(new ThreadStart(Save));
                    aSavingThread.Priority = ThreadPriority.Highest;
                    aSavingThread.Start();
                }
#if (PocketPC)
                try
                {
                    if (interfaceActivityThread != null)
                        interfaceActivityThread.Abort();
                }
                catch
                {
                }

                try
                {
                    if (dataCollectionThread != null)
                        dataCollectionThread.Abort();
                }
                catch
                {
                }

                try
                {
                    if (activityListenerThread != null)
                        activityListenerThread.Abort();
                }
                catch
                {
                }
#endif
            }

                //If bursty spawn interface tracking thread//data writing
                //termination thread
                //wakeup thread
            else if (this._TMode == TransmissionMode.Bursty60)
            {

                try
                {
                    if (aSavingThread != null)
                        aSavingThread.Abort();
                }
                catch
                {
                }

#if (PocketPC)
                countSeconds = new bool[this._Sensors.Count];
                LastACIndex = new int[this._Sensors.Count];
                LastSeqNum = new int[this._Sensors.Count];
                for (int i = 0; (i < this._Sensors.Count); i++)
                {
                    this._Sensors[i]._Loaded = true;
                    this._Sensors[i]._Flush = true;
                    this._Sensors[i]._RootStorageDirectory = this._StorageDirectory + "\\data\\raw\\PLFormat\\";
                    countSeconds[i] = false;
                    LastACIndex[i] = -1;
                    LastSeqNum[i] = -1;
                }

                reminderDateTime = DateTime.Now.AddSeconds(60);
                //default is local memory
                interfaceActivityThread = new Thread(new ThreadStart(InterfaceActivityTracker));
                interfaceActivityThread.Priority = ThreadPriority.Highest;
                dataCollectionThread = new Thread(new ThreadStart(DataCollection));
                //terminationThread = new Thread(new ThreadStart(TerminateWockets));
                //terminationThread.Start();
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
#endif
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


        int reminderID = 0;

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

#if (PocketPC)
        bool[] countSeconds = null;
        bool connecting = false;
        public int[] LastACIndex;
        public int[] LastSeqNum;
        void InterfaceActivityTracker()
        {

            int k = 0;
            int[] dataSavedSeconds = new int[this._Sensors.Count];
            int[] secondsCounter = new int[this._Sensors.Count];
            int[] full = new int[this._Sensors.Count];
            int[] partial = new int[this._Sensors.Count];
            int[] empty = new int[this._Sensors.Count];

            if (!Directory.Exists(this._StorageDirectory + "\\log\\"))
                Directory.CreateDirectory(this._StorageDirectory + "\\log\\");
            if (!Directory.Exists(this._StorageDirectory + "\\data\\summary\\"))
                Directory.CreateDirectory(this._StorageDirectory + "\\data\\summary\\");


            for (int i = 0; (i < this._Sensors.Count); i++)
            {
                dataSavedSeconds[i] = 0;
                secondsCounter[i] = 0;
                full[i]=0;
                partial[i]=0;

            }
            while (true)
            {
                if (connecting)
                {
                    SystemIdleTimerReset();
                    if ((this != null) && (this._Sensors.Count > 0))
                    {
                        //Check 2 things, num of connection failures
                        // check if data received is > 0
                        // if num connections >2, ready to pause
                        // if data received is >0, ready to pause within 2 seconds.

                        bool receiveFailed = true;
                        bool receivedFullData = true;
                        bool notimeoutData = true;
                        for (int i = 0; (i < this._Sensors.Count); i++)
                        {
                            receivedFullData &= (this._Sensors[i]._ReceivedPackets == ((WocketsDecoder)this._Decoders[i])._ExpectedBatchCount);

                            //halt, if either 1 successful connection was made
                            // or any data was received
                            // or 3 or more reconnections were made
                            if ((((RFCOMMReceiver)this._Receivers[i])._Reconnections < 3))
                                receiveFailed = false;

                            //if (((RFCOMMReceiver)this._Receivers[i])._SuccessfulConnections >= 1)
                            secondsCounter[i] = secondsCounter[i] + 1;

                            notimeoutData &= (secondsCounter[i] > 20);
                        }

                        if ((receivedFullData) || (receiveFailed) || (notimeoutData))
                        {

                           // for (int kk = 0; (kk < 10); kk++)
                            //{
                            for (int i = 0; (i < this._Sensors.Count); i++)
                            {
                                /* if (LastSeqNum[i] >= 0)
                                 {
                                     //System.IO.TextWriter tww = new StreamWriter("hELLO.txt",true);
                                     ((RFCOMMReceiver)this._Receivers[i]).Write(new ACK(LastSeqNum[i])._Bytes);
                                     //tww.WriteLine(LastSeqNum[i]);
                                     //tww.Close();
                                     Logger.Warn("Ack," + LastSeqNum[i]);
                                 }*/
                                //Core.WRITE_RECEIVED_ACs(i,((WocketsDecoder)this._Decoders[i])._ACIndex);
                                if (((WocketsDecoder)this._Decoders[i])._ACIndex == 10)
                                {
                                   // for (int kk = 0; (kk < 10); kk++)
                                        //((RFCOMMReceiver)this._Receivers[i]).Write(new ACK()._Bytes);
                                 //       ((RFCOMMReceiver)this._Receivers[i]).Write(new ACK(LastSeqNum[i])._Bytes);
                                }

                            }
                              //  Thread.Sleep(20);
                            //}
   


                            // if didnt get full data, sleep for 2 seconds
                            if (!receivedFullData)
                                Thread.Sleep(3000);

                            //save whatever we have so far then sleep
                            connecting = false;
                            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                            DateTime now = DateTime.Now;
                            double unixtime = WocketsTimer.GetUnixTime(now);
                            string currentTime = now.ToString("yyyy-MM-dd HH:mm:ss");
                            string log_line = ++k + "," + currentTime + "," + bpower.BatteryLifePercent + "," + bpower.BatteryVoltage + "," + bpower.BatteryCurrent + "," + bpower.BatteryTemperature;
                            string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                            
                            
                            for (int i = 0; (i < this._Sensors.Count); i++)
                            {

                                Core.WRITE_RECEIVED_COUNT(i, this._Sensors[i]._ReceivedPackets);
                                if (this._Sensors[i]._ReceivedPackets == ((WocketsDecoder)this._Decoders[i])._ExpectedBatchCount)
                                    full[i] = full[i] + 1;
                                else if (this._Sensors[i]._ReceivedPackets ==0)
                                    empty[i] = empty[i] + 1;
                                else
                                    partial[i] = partial[i] + 1;
                                
                                Core.WRITE_FULL_RECEIVED_COUNT(i,full[i]);
                                Core.WRITE_PARTIAL_RECEIVED_COUNT(i, partial[i]);
                                Core.WRITE_EMPTY_RECEIVED_COUNT(i, empty[i]);

                                log_line += "," + this._Sensors[i]._ReceivedPackets + "," + ((WocketsDecoder)this._Decoders[i])._ExpectedBatchCount + "," + ((RFCOMMReceiver)this._Receivers[i])._SuccessfulConnections + "," + ((RFCOMMReceiver)this._Receivers[i])._Reconnections + "," + ((RFCOMMReceiver)this._Receivers[i])._ConnectionTime;
                                dataSavedSeconds[i] = 0;
                                countSeconds[i] = false;
                                secondsCounter[i] = 0;
                                ((WocketsDecoder)this._Decoders[i])._ExpectedBatchCount = -1;


                                if (!Directory.Exists(this._StorageDirectory + "\\data\\summary\\" + hourlyPath))                                
                                    Directory.CreateDirectory(this._StorageDirectory + "\\data\\summary\\" + hourlyPath);                                

                                TextWriter tw2 = new StreamWriter(this._StorageDirectory+ "\\data\\summary\\"+hourlyPath+"\\Sensor-" + this._Sensors[i]._Location + "-" + i + ".csv", true);
                                int nextACIndex = LastACIndex[i] + 1;
                                if (nextACIndex == 960)
                                    nextACIndex = 0;
                                int countsaved = 0;
                                for (int j = nextACIndex; (j != ((WocketsDecoder)this._Decoders[i])._ActivityCountIndex); )
                                {
                                    DateTime ac_dt = new DateTime();
                                    WocketsTimer.GetDateTime((long)((WocketsDecoder)this._Decoders[i])._ActivityCounts[j]._TimeStamp, out ac_dt);
                                    string ac_currentTime = ac_dt.ToString("yyyy-MM-dd HH:mm:ss");
                                    tw2.WriteLine(DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss")+","+j+","+((WocketsDecoder)this._Decoders[i])._ActivityCounts[j]._SeqNum + "," + ac_currentTime + "," + ((WocketsDecoder)this._Decoders[i])._ActivityCounts[j]._TimeStamp + "," + ((WocketsDecoder)this._Decoders[i])._ActivityCounts[j]._Count);
                                    LastSeqNum[i] = ((WocketsDecoder)this._Decoders[i])._ActivityCounts[j]._SeqNum;
                                    LastACIndex[i] = j;
                                    countsaved++;
                                    j++;
                                    if (j == 960)
                                        j = 0;
                                }                              
                                Core.WRITE_SAVED_ACs(i, countsaved);
                                tw2.Close();                                
                            }

                            this._Polling = false;

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

                            //TextWriter tw = new StreamWriter(this._StorageDirectory + "\\data\\log\\" + hourlyPath + "\\stats.csv", true);
                            Logger.Log(log_line);
                            //tw.Close();




                            SystemIdleTimerReset();
                            for (int i = 0; (i < this._Sensors.Count); i++)
                            {
                                try
                                {
                                    this._Sensors[i].Save();
                                }
                                catch(Exception e)
                                {
                                    Logger.Error("Sensor " + i + ": failed to save:" + e.Message);
                                }
                            }

                            Thread.Sleep(1000);
                            if (DateTime.Now.Subtract(lastActivity).TotalSeconds > 30)
                              SetSystemPowerState(null, POWER_STATE_SUSPEND, POWER_FORCE);

                        }

                    }
                }

                Thread.Sleep(1000);
            }
        }

        
        void DataCollection()
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
                for (int i = 0; (i < this._Sensors.Count); i++)
                {
                    countSeconds[i] = true;
                    ((WocketsDecoder)this._Decoders[i])._ExpectedBatchCount = -1;
                    this._Sensors[i]._ReceivedPackets = 0;
                    ((RFCOMMReceiver)this._Receivers[i])._Reconnections = 0;
                }
                connecting = true;
                this._Polling = true;



                namedEvent.Reset();
                CeClearUserNotification((int)notificationHandle);
            }
        }
        private  void activityListener()
        {
            while (true)
            {
                // waiting for activity signal, will block the thread, works globally.
                WaitForSingleObject(activitySignal, int.MaxValue);
                lastActivity = DateTime.Now;
                Thread.Sleep(5000);
            }
        }

        /*private void TerminateWockets()
        {
            NamedEvents namedEvent = new NamedEvents();
            namedEvent.Receive("TerminateWockets");
            System.Diagnostics.Process.GetCurrentProcess().Kill();
        }*/

        private DateTime lastActivity = DateTime.Now;
        DateTime reminderDateTime;
        Thread interfaceActivityThread;
        Thread dataCollectionThread;
        //Thread terminationThread;

        private int EVENT_ALL_ACCESS = 0x1F0003;
        private  String ActiveName = "PowerManager/UserActivity_Active";
        private IntPtr activitySignal;
        private Thread activityListenerThread;
        [DllImport("coredll.dll")]
        private static extern IntPtr OpenEvent(int desiredAccess, bool inheritHandle, string name);

        [DllImport("coredll.dll")]
        private static extern int WaitForSingleObject(IntPtr handle, int milliseconds);

#endif           

        public void Dispose()
        {


            if (aPollingThread != null)            
                aPollingThread.Abort();            

            if (aSavingThread != null)                            
                aSavingThread.Abort();            

        
            if (trainingTW != null)
            {
                trainingTW.Flush();
                trainingTW.Close();
                trainingTW = null;
            }
            if (structureTW != null)
            {
                structureTW.Flush();
                structureTW.Close();
                structureTW = null;
            }
            for (int i = 0; (i < this._Receivers.Count); i++)
            {
                //this._Receivers[i]._Status = ReceiverStatus.Disconnected;
                //Thread.Sleep(100);                
                if (this._Sensors[i]._Loaded)
                {
                    this._Receivers[i].Dispose();
                    Thread.Sleep(1000);
                }
            }

            for (int i = 0; (i < this._Sensors.Count); i++)
                if (this._Sensors[i]._Loaded)
                {
                    this._Sensors[i].Dispose();
                    this._Decoders[i].Dispose();
                }

            
            //NetworkStacks._BluetoothStack.Dispose();

        }

        private void Save()
        {
            while (true)
            {
                if (!this.saving)
                {
                    this.waitToSaveEvent.Set();
                    this.savingEvent.WaitOne();
                }

                for (int i = 0; (i < this._Sensors.Count); i++)
                {
                    try
                    {
                        this._Sensors[i].Save();
                        Thread.Sleep(1000);
                    }
                    catch (Exception ee)
                    {
                        Logger.Error(ee.Message);
                    }
                }
            }
        }

        public Annotation _currentRecord
        {
            get
            {
                return this.currentRecord;
            }
            set
            {
                this.currentRecord = value;
            }
        }

        public Session _annotatedSession
        {
            get
            {
                return this.annotatedSession;
            }
            set
            {
                this.annotatedSession = value;
            }
        }



        public Instances _instances
        {
            get
            {
                return this.instances;
            }
            set
            {
                this.instances = value;
            }
        }

        public Classifier _classifier
        {
            get
            {
                return this.classifier;
            }
            set
            {
                this.classifier = value;
            }
        }



        private void Train()
        {

            TextWriter trainingTW = null;
            TextWriter structureTW = null;
            Hashtable labelIndex = new Hashtable();
            string arffFileName;

            while (true)
            {

                if (!this.training)
                    this.trainingEvent.WaitOne();

                #region Training
                //create arff file
                if (trainingTW == null)
                {
                    arffFileName = "output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";
                    trainingTW = new StreamWriter(arffFileName);
                    trainingTW.WriteLine("@RELATION wockets");
                    string arffHeader = FullFeatureExtractor.GetArffHeader();
                    arffHeader += "\n@ATTRIBUTE activity {";
                    int i = 0;
                    for (i = 0; (i < ((this.annotatedSession.OverlappingActivityLists[0]).Count - 1)); i++)
                        arffHeader += this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + ",";
                    arffHeader += this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + "}\n";
                    arffHeader += "\n@DATA\n\n";



                    trainingTW.WriteLine(arffHeader);
                    string structureArffFile = "structure.arff";
                    structureTW = new StreamWriter(structureArffFile);
                    structureTW.WriteLine("@RELATION wockets");
                    structureTW.WriteLine(arffHeader);

                }
                string current_activity = "unknown";
                if (this.currentRecord != null)
                {
                    double lastTimeStamp = FullFeatureExtractor.StoreWocketsWindow();
                    if (FullFeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                    {
                        current_activity = this.currentRecord.Activities._CurrentActivity;
                        string arffSample = FullFeatureExtractor.toString() + "," + current_activity;
                        trainingTW.WriteLine(arffSample);
                        extractedVectors++;
                        if (structureFileExamples < 10)
                        {
                            structureTW.WriteLine(arffSample);
                            structureFileExamples++;
                        }
                    }

                }
                else
                {
                    if (trainingTW != null)
                    {
                        structureTW.Flush();
                        structureTW.Close();
                        structureTW = null;
                        trainingTW.Flush();
                        trainingTW.Close();
                        trainingTW = null;
                    }
                }
                #endregion Training

                Thread.Sleep(50);
            }

        }

        private void Classify()
        {
            int[] labelCounters = null;
            Classifier classifier = null;
            FastVector fvWekaAttributes;
            Instances instances = null;
            string[] activityLabels = null;
            Hashtable labelIndex = new Hashtable();         
            int classificationCounter = 0;


            while (true)
            {

                if (!this.classifying)
                    this.classifyingEvent.WaitOne();

                if (classifier == null)
                {
                    classifier = new J48();
                    if (!File.Exists("/model.xml"))
                    {
                        string[] arffFiles = Directory.GetFileSystemEntries("/", "output*.arff");
                        if (arffFiles.Length != 1)
                            throw new Exception("Multiple Arff Files in Directory");
                        instances = new Instances(new StreamReader(arffFiles[0]));
                        instances.Class = instances.attribute(FullFeatureExtractor.ArffAttributeLabels.Length);
                        classifier.buildClassifier(instances);
                        TextWriter tc = new StreamWriter("/model.xml");
                        classifier.toXML(tc);
                        tc.Flush();
                        tc.Close();
                    }
                    else
                    {
                        instances = new Instances(new StreamReader("/structure.arff"));
                        instances.Class = instances.attribute(FullFeatureExtractor.ArffAttributeLabels.Length);
                        classifier.buildClassifier("/model.xml", instances);
                    }


                    fvWekaAttributes = new FastVector(FullFeatureExtractor.ArffAttributeLabels.Length + 1);
                    for (int i = 0; (i < FullFeatureExtractor.ArffAttributeLabels.Length); i++)
                        fvWekaAttributes.addElement(new weka.core.Attribute(FullFeatureExtractor.ArffAttributeLabels[i]));

                    FastVector fvClassVal = new FastVector();
                    labelCounters = new int[this.annotatedSession.OverlappingActivityLists[0].Count + 1];
                    activityLabels = new string[this.annotatedSession.OverlappingActivityLists[0].Count + 1];
                    for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists[0].Count); i++)
                    {
                        labelCounters[i] = 0;
                        string label = "";
                        int j = 0;
                        for (j = 0; (j < this.annotatedSession.OverlappingActivityLists.Count - 1); j++)
                            label += this.annotatedSession.OverlappingActivityLists[j][i]._Name.Replace(' ', '_') + "_";
                        label += this.annotatedSession.OverlappingActivityLists[j][i]._Name.Replace(' ', '_');
                        activityLabels[i] = label;
                        labelIndex.Add(label, i);
                        fvClassVal.addElement(label);
                    }
                }
                else
                {
                    double lastTimeStamp = FullFeatureExtractor.StoreWocketsWindow();
                    if (FullFeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                    {
                        Instance newinstance = new Instance(instances.numAttributes());
                        newinstance.Dataset = instances;
                        for (int i = 0; (i < FullFeatureExtractor.Features.Length); i++)
                            newinstance.setValue(instances.attribute(i), FullFeatureExtractor.Features[i]);
                        double predicted = classifier.classifyInstance(newinstance);
                        string predicted_activity = newinstance.dataset().classAttribute().value_Renamed((int)predicted);

                        int currentIndex = (int)labelIndex[predicted_activity];
                        labelCounters[currentIndex] = (int)labelCounters[currentIndex] + 1;
                        classificationCounter++;

                        if (classificationCounter == 5)
                        {
                            classificationCounter = 0;
                            int mostCount = 0;
                            string mostActivity = "";
                            //Color indicate;
                            //int level;
                            for (int j = 0; (j < labelCounters.Length); j++)
                            {
                                // level = 240 - 240 * labelCounters[j] / configuration._SmoothWindows;
                                //indicate = Color.FromArgb(level, level, level);
                                //this.ActGUIlabels[j].ForeColor = indicate;
                                //this.ActGUIlabels[j].Invalidate();
                                if (labelCounters[j] > mostCount)
                                {
                                    mostActivity = activityLabels[j];
                                    mostCount = labelCounters[j];
                                }
                                labelCounters[j] = 0;
                            }

                        }
                    }
                }


                Thread.Sleep(50);
            }

        }




        public static object MyLock = new object();

        private void Poll()
        {
            #region Poll All Wockets and MITes and Decode Data

            if ((this._Mode == MemoryMode.BluetoothToLocal) || (this._Mode == MemoryMode.BluetoothToShared))
            {
                bool allWocketsDisconnected = true;
                bool bluetoothIsReset = false;
                Receiver currentReceiver = null;
                Sensor sensor = null;

                int[] batteryPoll = new int[this._Sensors.Count];
                int[] alive = new int[this._Sensors.Count];

                GET_BT GET_BT_CMD = new GET_BT();
                ALIVE ALIVE_CMD = new ALIVE();
                int pollCounter = 0;

                System.Reflection.Assembly a = System.Reflection.Assembly.GetExecutingAssembly();
                System.Reflection.AssemblyName an = a.GetName();
                Logger.Warn("Version " + an.Version.ToString() +" Date:"+ DateTime.Now.ToString("f"));
                this.StartTime = WocketsTimer.GetUnixTime();

                while (true)
                {

                    if (!polling)
                    {
                        this.waitToPollEvent.Set();
                        for (int i = 0; (i < this._Sensors.Count); i++)
                        {
                            this._Sensors[i]._ReceivedPackets = 0;
                            this._Sensors[i]._SavedPackets = 0;                            
                            this._Receivers[i].Dispose();
                        }
                        this.pollingEvent.WaitOne();
                    }

                    allWocketsDisconnected = true;
                    pollCounter++;

                    for (int i = 0; (i < this._Sensors.Count); i++)
                    {

                        sensor = this._Sensors[i];
                        if (sensor._Loaded)
                        {
                            currentReceiver = sensor._Receiver;
                            try
                            {
                                if (this._TMode== TransmissionMode.Bursty60)
                                {

                                    int expectedPackets = ((Wockets.Decoders.Accelerometers.WocketsDecoder)sensor._Decoder)._ExpectedBatchCount;
                                    //skip if got everything
                                    if ((expectedPackets > 0) && (sensor._ReceivedPackets == expectedPackets))
                                        continue;
                                    else
                                        currentReceiver.Update();
                                }
                                else
                                    currentReceiver.Update();



                                if (currentReceiver._Status == ReceiverStatus.Connected)
                                {
                                    Decoder decoder = sensor._Decoder;
                                    int numDecodedPackets = 0;
                                    int tail = currentReceiver._Buffer._Tail;
                                    int head = currentReceiver._Buffer._Head;

                                    int dataLength = tail - head; //((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail - currentReceiver._Head;
                                    if (dataLength < 0)
                                        dataLength = currentReceiver._Buffer._Bytes.Length - head + tail;//((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer.Length - currentReceiver._Head + ((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail;

                                    //test if all wockets are disconnected
                                    if (sensor._Class == SensorClasses.Wockets)
                                    {
                                        if (bluetoothIsReset)
                                            bluetoothIsReset = false;

                                        if (allWocketsDisconnected)
                                            allWocketsDisconnected = false;
                                    }

                                    if (dataLength > 0)
                                    {
                                        if (currentReceiver._Type == ReceiverTypes.HTCDiamond)
                                        {
                                            numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail);
                                            sensor._ReceivedPackets += numDecodedPackets;
                                        }
                                        else if (sensor._Class == SensorClasses.Wockets)
                                        {

                                            #region Write Data
                                            #region Battery Query
                                            batteryPoll[i] -= 1;
                                            if (batteryPoll[i] <= 0)
                                            {
                                                ((SerialReceiver)currentReceiver).Write(GET_BT_CMD._Bytes);
                                                batteryPoll[i] = 6000 + i * 200;
                                            }
                                            #endregion Battery Query

                                            #region Alive
                                            alive[i] -= 1;
                                            if (alive[i] <= 0)
                                            {
                                                ((SerialReceiver)currentReceiver).Write(ALIVE_CMD._Bytes);                                                
                                                alive[i] = 200;
                                            }
                                            #endregion Alive

                                            #endregion Write Data

                                            #region Read Data

                                            numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail); //((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer, head, tail);
                                            currentReceiver._Buffer._Head = tail;
                                            sensor._ReceivedPackets += numDecodedPackets;
                                            #endregion Read Data
                                        }

                                    }

                                    if (pollCounter > 2000)
                                    {
                                        //Logger.Warn("Receiver " + sensor._Receiver._ID + " decoded:" + sensor._ReceivedPackets + ",saved:" + sensor._SavedPackets + ", tail=" + tail + ",head=" + head);
                                        pollCounter = 0;
                                    }

                                }

                            }

                            catch (Exception ex)
                            {
                                alive[i] = 200;//10 in sniff//200 in continuous worked well
                                Logger.Error(ex.Message + " \nTrace:" + ex.StackTrace);
                                currentReceiver.Dispose();
                            }
                        }
                    }

                    //reset bluetooth stack once if all wockets are disconnected

                    if ((this._TMode== TransmissionMode.Continuous) && (!bluetoothIsReset) && (allWocketsDisconnected))
                    {
                        try
                        {
                            //if (CurrentWockets._Configuration._SoftwareMode == Wockets.Data.Configuration.SoftwareConfiguration.DEBUG)
                              //  Logger.Debug("All Wockets Disconnected. BT Reset.");
                            NetworkStacks._BluetoothStack.Dispose();
                            NetworkStacks._BluetoothStack.Initialize();
                            bluetoothIsReset = true;
                        }
                        catch
                        {
                        }
                    }

                    Thread.Sleep(10);
                }




            }
#if (PocketPC)
            //Read data from shared memory and populate the decoder
            else if (this._Mode == MemoryMode.SharedToLocal)
            {
                MemoryMappedFileStream[] sdata = null;
                MemoryMappedFileStream[] shead = null;
                byte[] head = new byte[4];
                int sdataSize = 0;
                int numSensors = CurrentWockets._Controller._Sensors.Count;
                int[] decoderTails;

                byte[] timestamp = new byte[sizeof(double)];
                byte[] acc = new byte[sizeof(short)];

                sdata = new MemoryMappedFileStream[numSensors];
                shead = new MemoryMappedFileStream[numSensors];
                sdataSize = (int)Decoder._DUSize * Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE;
                decoderTails = new int[numSensors];
                for (int i = 0; (i < numSensors); i++)
                {
                    sdata[i] = new MemoryMappedFileStream("\\Temp\\wocket" + i + ".dat", "wocket" + i, (uint)sdataSize, MemoryProtection.PageReadWrite);
                    shead[i] = new MemoryMappedFileStream("\\Temp\\whead" + i + ".dat", "whead" + i, sizeof(int), MemoryProtection.PageReadWrite);

                    sdata[i].MapViewToProcessMemory(0, sdataSize);
                    shead[i].MapViewToProcessMemory(0, sizeof(int));

                    shead[i].Read(head, 0, 4);
                    int currentHead = BitConverter.ToInt32(head, 0);
                    decoderTails[i] = currentHead;
                    shead[i].Seek(0, System.IO.SeekOrigin.Begin);
                    sdata[i].Seek((currentHead * (sizeof(double) + 3 * sizeof(short))), System.IO.SeekOrigin.Begin);

                }


                while (true)
                {
                    try
                    {
                        for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                        {
                            int tail = decoderTails[i];
                            int currentHead = tail;
                            shead[i].Read(head, 0, 4);
                            currentHead = BitConverter.ToInt32(head, 0);
                            shead[i].Seek(0, System.IO.SeekOrigin.Begin);

                            while (tail != currentHead)
                            {

#if (PocketPC)
                                int bufferHead = CurrentWockets._Controller._Decoders[i]._Head;
                                WocketsAccelerationData datum = ((WocketsAccelerationData)CurrentWockets._Controller._Decoders[i]._Data[bufferHead]);
                                datum.Reset();
                                datum._SensorID = (byte)i;
                                sdata[i].Read(timestamp, 0, sizeof(double));
                                datum.UnixTimeStamp = BitConverter.ToDouble(timestamp, 0);
                                sdata[i].Read(acc, 0, sizeof(short));
                                datum._X = BitConverter.ToInt16(acc, 0);
                                sdata[i].Read(acc, 0, sizeof(short));
                                datum._Y = BitConverter.ToInt16(acc, 0);
                                sdata[i].Read(acc, 0, sizeof(short));
                                datum._Z = BitConverter.ToInt16(acc, 0);
                                datum._Type = Data.SensorDataType.UNCOMPRESSED_DATA_PDU;
                                CurrentWockets._Controller._Decoders[i].TotalSamples++;

                                //copy raw bytes
                                //for (int i = 0; (i < bytesToRead); i++)
                                //  datum.RawBytes[i] = this.packet[i];

                                //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));


                                if (bufferHead >= (CurrentWockets._Controller._Decoders[i]._BufferSize - 1))
                                    bufferHead = 0;
                                else
                                    bufferHead++;
                                CurrentWockets._Controller._Decoders[i]._Head = bufferHead;

#endif


                                if (tail >= (Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE - 1))
                                {
                                    tail = 0;
#if (PocketPC)
                                    sdata[i].Seek(0, System.IO.SeekOrigin.Begin);
#endif
                                }
                                else
                                    tail++;
                            }

                            decoderTails[i] = currentHead;
                        }
                    }
                    catch
                    {
                    }
                    Thread.Sleep(100);
                }


            }
#endif

            #endregion Poll All Wockets and MITes and Decode Data
        }

        #region Serialization Methods
        public string ToXML()
        {
            string xml = "<" + SENSORDATA_ELEMENT + ">\n";
            xml += this._Receivers.ToXML();
            xml += this._Decoders.ToXML();
            xml += this._Sensors.ToXML();
            xml += "</" + SENSORDATA_ELEMENT + ">\n";
            return xml;
        }

        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == SENSORDATA_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == ReceiverList.RECEIVERS_ELEMENT)
                        this._Receivers.FromXML(jNode.OuterXml);
                    else if (jNode.Name == DecoderList.DECODERS_ELEMENT)
                        this._Decoders.FromXML(jNode.OuterXml);
                    else if (jNode.Name == SensorList.SENSORS_ELEMENT)
                    {
                        //the sensor by default loads with a generic decoder as a place holder with its ID set
                        //to point to the right decoder in this.decoders
                        this._Sensors.FromXML(jNode.OuterXml);

                        //the decoder references for the sensor have to be updated correctly
                        for (int i = 0; (i < this._Sensors.Count); i++)
                            this._Sensors[i]._Decoder = this._Decoders[this._Sensors[i]._Decoder._ID];
                        for (int i = 0; (i < this._Sensors.Count); i++)
                            this._Sensors[i]._Receiver = this._Receivers[this._Sensors[i]._Receiver._ID];
                    }
                }
            }
        }
        #endregion Serialization Methods
    }
}
