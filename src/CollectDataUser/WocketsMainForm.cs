using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Collections;
using System.Threading;
using System.IO;
using System.Runtime.InteropServices; //For DllImports
using System.Diagnostics; //Processes related functions
using Microsoft.WindowsCE.Forms;

using Wockets;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets.Data.Types;
using Wockets.Receivers;
using Wockets.Utils;
using Wockets.Utils.IPC;


namespace CollectDataUser
{



    public partial class WocketsMainForm : Form
    {


      #region Variables

        //General Status Variables
        private String sensor_set = "";
        private String app_status = "";
        private String software_version = "";

        //Wockets Controller
        private WocketsController wockets_controller; 
        private Thread startupThread;    //starts kernel and load wockets
        private ArrayList sensors_list;  

        //Data Uploader
        private Thread uploadThread;
        private static System.Diagnostics.Process _UploaderProcess = null;

        //Application Running Elapsed Time
        private string ElapsedTime = "00days  00h:00m:00s";
        
        //uploaded files counters
        private bool disposed = false;
        private int counter = 0;
        private int prevSuccessful = -1; 
        private int prevFailed = -1;
        //private int uploadCounter = 0;


        //ACs for sensors status
        public string _Full = "";
        public string _Lost = "";
        public string _Partial = "";
        public int    _ID = 0;
        System.Windows.Forms.Timer ACsUpdateTimer;


        //System Wide Lock
        public static string APP_LOCK = "APPLock";
        private static Semaphore appLock = new Semaphore(1, 1, APP_LOCK);

        //Internal Message Window
        private internalMessageWindow messageWindow;
        public IntPtr wndPtr;

        //-- PInvokes --
        //Find the Internal Message Window
        [DllImport("coredll.dll")]
        public static extern IntPtr FindWindow(string lpClassName, string lpWindowName);

        //Minimize the Window Form
        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
        const int SW_MINIMIZED = 6;
        const int SW_NORMAL = 1;

        //Connection Status Monitoring
        private int[] PrevFullPkg;
        private int[] PrevPartialPkg;
        private int[] PrevEmptyPkg;
        private DateTime[] LastPkgTime;
        private TimeSpan[] ElapsedConnectionTime;
        
        #endregion 


      #region Initialize Form


        public WocketsMainForm()
        {

            InitializeComponent();


            #region Initialize Internal Message Window

            appLock.WaitOne();

            string MsgWindowName = "WocketsMessageWindow";
            IntPtr hndl = new IntPtr();
            hndl = FindWindow(null, MsgWindowName);


            try
            {
                //Check if the internal message window exists
                if (hndl == IntPtr.Zero)
                {

                    //Initialize the internal message window
                    this.messageWindow = new internalMessageWindow(this);
                    wndPtr = this.messageWindow.Hwnd;

                    //Assign a name to the Main Form
                    this.Text = "WocketsApp";

                    //Wait to ensure the message window is registered
                    Thread.Sleep(1000);
                }
                else
                {
                    appLock.Release();
                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();

                }

            }
            finally
            {
                appLock.Release();
            }


            #endregion  Initialize Internal Message Window



            #region Identify the Storage Card

            string firstCard = "";
            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();


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

            Settings._StorageDirectory = firstCard;

            #endregion

            #region Initialize the Logger
            Logger.InitLogger(firstCard + "\\applog\\");
            Logger.Debug("Starting Application");

            #endregion


            #region Read the Sowftware Version
            System.Reflection.Assembly a = System.Reflection.Assembly.GetExecutingAssembly();
            System.Reflection.AssemblyName an = a.GetName();
            software_version = "Version " + an.Version.ToString();
            this.label_software_version.Text = software_version;
            #endregion


            #region Read Phone IMEI

            label_phone_IMEI.Text = CurrentPhone._IMEI;

            #endregion


            #region Read the last sensor set, kernel status, and master list files

            #region Read the last sensor set

            try
            {
                if (File.Exists(Core.KERNEL_PATH + "\\updater_last_set.txt"))
                {
                    StreamReader tr_sensors = new StreamReader(Core.KERNEL_PATH + "\\updater_last_set.txt");
                    this.sensor_set = tr_sensors.ReadLine();
                    tr_sensors.Close();

                    if (this.sensor_set.CompareTo("") == 0)
                    { this.sensor_set = "red"; }
                }
                else
                {   //set red as the default set
                    this.sensor_set = "red";
                }
            }
            catch
            {
                this.sensor_set = "red";
            }

            #endregion



            #region Read the last kernel status

            try
            {
                if (File.Exists(Core.KERNEL_PATH + "\\updater_last_status.txt"))
                {
                    StreamReader tr_status = new StreamReader(Core.KERNEL_PATH + "\\updater_last_status.txt");
                    app_status = tr_status.ReadLine();
                    tr_status.Close();

                    if (this.app_status.CompareTo("") == 0)
                    { this.sensor_set = "normal_start"; }
                }
                else
                {
                    //set the app to start from beginning
                    this.app_status = "normal_start";
                }
            }
            catch
            {
                this.app_status = "normal_start";
            }

            #endregion



            #region Read Master List File

            //string[] sensor_data;
            //try
            //{
            //    if (File.Exists(Core.KERNEL_PATH + "\\MasterListTemplate.txt"))
            //    {
            //        StreamReader tr_sensors_data = new StreamReader(Core.KERNEL_PATH + "\\MasterListTemplate.txt");
            //        string rline = tr_sensors_data.ReadLine();
            //        sensor_data = rline.Split(',');
            //        tr_sensors_data.Close();
            //    }
            //}
            //catch
            //{  //AppLogger.WriteLine("sensor master file couldn't be access correctly.");
            //}

            #endregion


            #endregion


            #region Load SensorData From XML

            wockets_controller = new Wockets.WocketsController("", "", "");

            //Check which sensor set was used in previous run
            if (this.sensor_set.CompareTo("red") == 0)
                wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
            else
                wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");


            // point kernel to wockets controller
            CurrentWockets._Controller = wockets_controller;

            //Load sensors addresses to array list
            sensors_list = new ArrayList();
            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);

            Logger.Debug("Sensor Info Loaded From Xml, Sensor Set: " + sensor_set);

            #endregion


            #region Check updates from master list

            #region === Sensors Master File Parameters ===
            // (Parameter = ID)
            // IMEI=0,
            // SetID_1=1,force_update_1=2,MAC_S1_1=3,MAC_S1_2=4
            // SetID_2=5,force_update_2=6,MAC_S2_1=7,MAC_S2_2=8
            #endregion
            //if (sensor_data != null)
            //{
            //    //Check which sensor set was used in previous run
            //    if (this.sensor_set.CompareTo(sensor_data[1]) == 0)
            //    {
            //        CurrentWockets._Controller.FromXML(Core.KERNEL_PATH + "\\updater_SensorData1.xml");
            //    }
            //    else if (this.sensor_set.CompareTo(sensor_data[5]) == 0)
            //    {
            //        CurrentWockets._Controller.FromXML(Core.KERNEL_PATH + "\\updater_SensorData2.xml");
            //    }


            //    #region If the sensors are different from the ones in the sensor master list, update controller settings

            //    // Inquire the sensor calibration parameters from the wocket 
            //    if ((((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address.CompareTo(sensor_data[3]) != 0))
            //    {
            //        //replace the mac address 
            //        ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address = sensor_data[3];
            //        //send commands to get the sensor calibration values & effective sampling rate
            //    }


            //    if ((((RFCOMMReceiver)CurrentWockets._Controller._Receivers[1])._Address.CompareTo(sensor_data[4]) != 0))
            //    {
            //        //replace the mac address
            //        ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[1])._Address = sensor_data[4];
            //        //send commands to get the sensor calibration values & effective sampling rate
            //    }

            //    #endregion

            //}

            #endregion


            #region Initialize Registry for Received Data Packages

            ResetACsCounters(wockets_controller);

            #endregion


            #region Suscribe to Kernel Events

            SuscribeToKernelEvents();

            #endregion


            #region Initialize Elapsed Time Counter On File Upload Screen

            //Hide the timer label
            textBox_elapsed_time.Visible = false;
            textBox_elapsed_time.Text = "00h:00m:00s";

            #endregion


            #region Initialize Sensors Data Received Status

            ACsUpdateTimer = new System.Windows.Forms.Timer();
            ACsUpdateTimer.Interval = 1000;
            ACsUpdateTimer.Tick += new EventHandler(ACsUpdateTimer_Tick);
            ACsUpdateTimer.Enabled = false;

            #endregion



            #region Try to connect to kernel, using the loaded settings

            if (app_status.CompareTo("normal_start") == 0)
            {
                //Hide the connect panel
                ConnectPanel.Enabled = false;
                ConnectPanel.Visible = false;

                //Hide the Main Actions Buttons Panel
                MainActionsPanel.Visible = false;
                MainActionsPanel.Enabled = false;

                //Hide the Sensor Status Panel
                SensorStatusPanel.Visible = false;
                SensorStatusPanel.Enabled = false;

                //Setup the main menu commands
                menuMainAppActions.Text = "Main Menu";
                menuQuitApp.Text = "Connect";

                //Show the swap panel
                SwapPanel.BringToFront();
                SwapPanel.Enabled = true;
                SwapPanel.Visible = true;


                //update the sensor set/swap panel
                Show_Swap_Panel("Disconnected", sensor_set, CurrentWockets._Controller);

                Logger.Debug("Connecting to Kernel in Normal Mode");

            }
            else
            {
                //Hide the swap panel
                SwapPanel.Enabled = false;
                SwapPanel.Visible = false;



                //Hide the Main Actions Buttons Panel
                MainActionsPanel.Visible = false;
                MainActionsPanel.Enabled = false;

                //Hide the Sensor Status Panel
                SensorStatusPanel.Visible = false;
                SensorStatusPanel.Enabled = false;

                //Show the connect panel
                ConnectPanel.BringToFront();
                ConnectPanel.Enabled = true;
                ConnectPanel.Visible = true;
                label_kernel_status.Text = "";

                //Start the kernel connection sequence
                StartLoadingWocketsToKernel();

                Logger.Debug("Connecting to Kernel in Silent Mode");

            }

            #endregion



            #region Connection Status Initialization

            PrevFullPkg = new int[wockets_controller._Receivers.Count];
            for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                PrevFullPkg[np] = 0;

            PrevPartialPkg = new int[wockets_controller._Receivers.Count];
            for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                PrevPartialPkg[np] = 0;

            PrevEmptyPkg = new int[wockets_controller._Receivers.Count];
            for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                PrevEmptyPkg[np] = 0;

            LastPkgTime = new DateTime[wockets_controller._Receivers.Count];
            for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                LastPkgTime[np] = DateTime.Now;

            ElapsedConnectionTime = new TimeSpan[wockets_controller._Receivers.Count];
            for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                ElapsedConnectionTime[np] = TimeSpan.Zero;


            #endregion


        }


     #endregion


      #region Swap Sensors

        private void Show_Swap_Panel(String status, String set, WocketsController wc)
        {
            try
            {

                SwapSensorsButton.Enabled = true;
                

                //sensors status
                if (status.CompareTo("Connected") == 0)
                {
                    textBox_sensors_status.Text = "Kernel Connected";
                    textBox_sensors_status.ForeColor = Color.Green;

                    //update the sensor status panel
                    textBox_spanel_sensors_status.Text = "Kernel Connected";
                    textBox_spanel_sensors_status.ForeColor = Color.Green;

                    //update fields in main app actions panel
                    textBox_main_sensor_status.Text = "Kernel Connected";
                    textBox_main_sensor_status.ForeColor = Color.Green;
                }
                else
                {
                    textBox_sensors_status.Text = "Kernel Disconnected";
                    textBox_sensors_status.ForeColor = Color.DimGray;

                    //update the sensor status panel
                    textBox_spanel_sensors_status.Text = "Kernel Disconnected";
                    textBox_spanel_sensors_status.ForeColor = Color.DimGray;

                    //update fields in main app actions panel
                    textBox_main_sensor_status.Text = "Kernel Disconnected";
                    textBox_main_sensor_status.ForeColor = Color.DimGray;
                }


                //sensors set
                if (sensor_set.CompareTo("red") == 0)
                {
                    textBox_sensor_set_ID.Text = "RED SET";
                    textBox_sensor_set_ID.BackColor = Color.Tomato;

                    //update sensors status panel
                    textBox_spanel_sensors_ID.Text = "RED SET";
                    textBox_spanel_sensors_ID.BackColor = Color.Tomato;

                    //update fields in main app actions panel
                    textBox_main_sensor_set_ID.Text = "RED SET";
                    textBox_main_sensor_set_ID.BackColor = Color.Tomato;
                }
                else
                {
                    textBox_sensor_set_ID.Text = "GREEN SET";
                    textBox_sensor_set_ID.BackColor = Color.YellowGreen;

                    //update sensors status panel
                    textBox_spanel_sensors_ID.Text = "GREEN SET";
                    textBox_spanel_sensors_ID.BackColor = Color.YellowGreen;

                    //update fields in main app actions panel
                    textBox_main_sensor_set_ID.Text = "GREEN SET";
                    textBox_main_sensor_set_ID.BackColor = Color.YellowGreen;
                }


                //sensors locations
                if (wc != null)
                {
                    if (wc._Receivers.Count > 0)
                    {
                        textBox_spanel_sensors_location_0.Text = textBox_sensor_location_0.Text = ((RFCOMMReceiver)wc._Receivers[0])._Address.Substring(7);

                        if (wc._Sensors[0]._Location != null)
                            textBox_spanel_sensors_location_0.Text = textBox_sensor_location_0.Text = textBox_sensor_location_0.Text + " At " + wc._Sensors[0]._Location.Substring(9) + ":";



                        if (CurrentWockets._Controller._Receivers.Count > 1)
                        {
                            textBox_spanel_sensors_location_1.Text = textBox_sensor_location_1.Text = ((RFCOMMReceiver)wc._Receivers[1])._Address.Substring(7);

                            if (wc._Sensors[1]._Location != null)
                                textBox_spanel_sensors_location_1.Text = textBox_sensor_location_1.Text = textBox_sensor_location_1.Text + " At " + wc._Sensors[1]._Location.Substring(9) + ":";

                        }
                    }
                }
            }
            catch 
            {
                Logger.Debug("Problem Reading Xml Parameters for Sensor Locations");
            }

        }

        private void SwapSensorsButton_Click(object sender, EventArgs e)
        {

            SwapSensorsButton.Enabled = false;
            Logger.Debug("Swapping Sensors Button Clicked");
            

            //Hide the connect status panel
            SwapPanel.Visible = false;
            SwapPanel.Enabled = false;

            //Show the connect status panel
            ConnectPanel.BringToFront();
            ConnectPanel.Visible = true;
            ConnectPanel.Enabled = true;

            try
            {
                if (app_status.CompareTo("running") == 0)
                {
                    //Disconnect current sensors set from kernel
                    Core.Disconnect();
                    UpdateMsg("Disconnect Wockets");
                    Logger.Debug("Sending Disconnect Command to Kernel");
                }
                else
                {
                    UpdateMsg("Swapping Wockets");
                    Logger.Debug("Start Swapping Sensors in Normal Mode. Kernel Not Connected.");

                    //TODO: Stop the elapsep time thread

                    //Dispose the old wockets controller
                    wockets_controller.Dispose();
                    wockets_controller = new Wockets.WocketsController("", "", "");


                    //Determine which set will be used & load the corresponding Xml File
                    if (this.sensor_set.CompareTo("red") == 0)
                    {
                        sensor_set = "green";
                        wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");
                    }
                    else
                    {
                        sensor_set = "red";
                        wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
                    }


                    //point the kernel to the wockets controller
                    CurrentWockets._Controller = wockets_controller;


                    //TODO: Check if macs against the master list file


                    //Add the sensors macs to the sensor list
                    sensors_list.Clear();
                    for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                        sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);


                    Thread.Sleep(1000);

                    //Hide the connect status panel
                    ConnectPanel.Visible = false;
                    ConnectPanel.Enabled = false;

                    //Show the swap panel
                    SwapPanel.BringToFront();
                    SwapPanel.Visible = true;
                    SwapPanel.Enabled = true;

                    //Update the swap interface
                    Show_Swap_Panel("Disconnected", sensor_set, wockets_controller);

                }
            }
            catch
            {
                Logger.Debug("Swapping After Button Click Filed");
            }

        }

      #endregion Swap Sensors



      #region Kernel Related Functions

        
       private void SuscribeToKernelEvents()
        {
            try
            {
                // Kernel response events that the application wants to listen to
                Core.SubscribeEvent(KernelResponse.STARTED, EventListener);
                Core.SubscribeEvent(KernelResponse.REGISTERED, EventListener);
                Core.SubscribeEvent(KernelResponse.UNREGISTERED, EventListener);
                Core.SubscribeEvent(KernelResponse.STOPPED, EventListener);
                Core.SubscribeEvent(KernelResponse.DISCOVERED, EventListener);
                Core.SubscribeEvent(KernelResponse.CONNECTED, EventListener);
                Core.SubscribeEvent(KernelResponse.DISCONNECTED, EventListener);
                Core.SubscribeEvent(KernelResponse.SENSORS_UPDATED, EventListener);
                Core.SubscribeEvent(KernelResponse.PING_RESPONSE, EventListener);

                Thread.Sleep(2000);
            }
            catch
            {
                Logger.Debug("Successfully suscribed to kernel events.");
            }
        }


       private void StartLoadingWocketsToKernel()
        {
            startupThread = new Thread(new ThreadStart(LoadWocketsToKernel));
            startupThread.Start();
        }


       private void LoadWocketsToKernel()
       {
           try
           {
               if (!Core._KernalStarted)
               {
                   if (!Core.Start())
                   {
                       MessageBox.Show("failed to start kernel");
                       Logger.Debug("failed to start kernel: msg 1");
                   }
                   else
                   {
                       Thread.Sleep(5000);
                       Logger.Debug("Kernel started successfully: msg1");
                   }
               }
               else
               {
                   //Make sure no kernels are running
                   if (Core.Terminate())
                   {
                       if (!Core.Start())
                       {
                           MessageBox.Show("Failed to start kernel");
                           Logger.Debug("Failed to start the kernel: msg2");
                       }
                       else
                       {
                           Thread.Sleep(5000);
                           Logger.Debug("Kernel started successfully: msg2");
                       }
                   }
                   else
                   {
                       MessageBox.Show("Failed to shutdown kernel");
                       Logger.Debug("Failed to shutdown the kernel");
                   }
               }

               Thread.Sleep(5000);
               Core.Ping();
               Logger.Debug("Ping Kernel");
           }
           catch
           {    
               Logger.Debug("An exception occurred when trying to start kernel."); 
           }
        }


       
       #region Kernel Response CallBacks and Event Listener

            delegate void UpdateFormCallback(KernelResponse response);
            /// Handles kernel response events
            private void EventListener(KernelResponse rsp)
            {
                try
                {
                    // InvokeRequired required compares the thread ID of the
                    // calling thread to the thread ID of the creating thread.
                    // If these threads are different, it returns true.
                    if (this.InvokeRequired || this.InvokeRequired)
                    {
                        UpdateFormCallback d = new UpdateFormCallback(EventListener);
                        this.Invoke(d, new object[] { rsp });
                    }
                    else
                    {

                        switch (rsp)
                        {
                            case KernelResponse.PING_RESPONSE:
                                Logger.Debug("Ping responsed received");
                                UpdateMsg("Register App");
                                Core.Register();
                                break;
                            case KernelResponse.STARTED:
                                Logger.Debug("Registered started response received");
                                UpdateMsg("Register App");
                                Core.Register();
                                break;
                            case KernelResponse.REGISTERED:
                                Logger.Debug("Registered finished response received");
                                UpdateMsg("Verify Wockets");
                                Core.SetSensors(this.sensors_list);
                                break;
                            case KernelResponse.SENSORS_UPDATED:
                                Logger.Debug("Sensors updated response received");
                                UpdateMsg("Connect Wockets");
                                Core.Connect(TransmissionMode.Bursty60);
                                
                                break;
                            case KernelResponse.CONNECTED:

                                Logger.Debug("connected response received");

                                //Wait for the system to stabilize (already included in start kernel thread)
                                //Thread.Sleep(4000);

                                #region Connect Sequence

                                //Write the connection status to panel screen
                                UpdateMsg("Wockets Connected");

                                //Wait for the system to stabilize
                                //Thread.Sleep(1000);


                                // Update Status Files
                               try
                                {
                                    Logger.Debug("start saving app status to files");

                                    //Set ID file
                                    //updates the sensor set used by kernel
                                    StreamWriter wr_sensors = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_set.txt");
                                    wr_sensors.WriteLine(sensor_set);
                                    wr_sensors.Flush();
                                    wr_sensors.Close();

                                    //indicates that the kernel is running
                                    app_status = "running";
                                    
                                   //Indicate that application was terminated by the user
                                    StreamWriter wr_status = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_status.txt");
                                    wr_status.WriteLine("running");
                                    wr_status.Flush();
                                    wr_status.Close();
                                }
                               catch 
                               { 
                                   Logger.Debug("An exception occurred when trying to save app status to files"); 
                               }


                               //Update the sensors status variable on the swap panel screen
                               Show_Swap_Panel("Connected", sensor_set, wockets_controller);
                               
                               //Hide the connect panel
                               ConnectPanel.Enabled = false;
                               ConnectPanel.Visible = false;
                               
                               //Show the swap panel
                               SwapPanel.BringToFront();
                               SwapPanel.Enabled = true;
                               SwapPanel.Visible = true;
                               
                              //Update the main application menu options
                               menuMainAppActions.Text = "Main Menu";

                               //Wait to stabilize system
                               //Thread.Sleep(1000);

                              //Start the connection status thread 
                              if( !ACsUpdateTimer.Enabled )
                                StartACsUpdater();

                              //Initialize the connection status timer
                              for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                                  LastPkgTime[np] = DateTime.Now;

                             
                              #endregion

                              Logger.Debug("Connection to wockets procedure finished");

                              break;


                            case KernelResponse.DISCONNECTED:

                              Logger.Debug("Disconnect from wockets response received");

                                //Stop the connection status thread 
                                if (ACsUpdateTimer.Enabled)
                                    StopACsUpdater();

                                //Stop Kernel (commented for now)
                                //if (TerminateKernel())
                                // UpdateMsg("Stop Kernel"); 

                                //Wait to stabilize system
                                Thread.Sleep(3000);

                                #region Swap Sequence

                                #region commented
                                //if disconnected, swap sensors if the app is running
                                //if (app_status.CompareTo("running") == 0){}
                                #endregion

                                try
                                {

                                    UpdateMsg("Swap Wockets");
                                    Logger.Debug("Starting to swap wockets, Current Set: " + sensor_set);

                                    //Dispose the old wockets controller
                                    wockets_controller.Dispose();
                                    Thread.Sleep(1000);
                                    Logger.Debug("Wockets controller disposed");


                                    //Create new wockets controller
                                    wockets_controller = new Wockets.WocketsController("", "", "");

                                    //Determine which set will be used & load the corresponding Xml File
                                    if (this.sensor_set.CompareTo("red") == 0)
                                    {
                                        sensor_set = "green";
                                        wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");
                                    }
                                    else
                                    {
                                        sensor_set = "red";
                                        wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
                                    }

                                    //TODO: Check if macs against the master list file
                                    //point kernel to new wockets controller
                                    CurrentWockets._Controller = wockets_controller;

                                    //Add the sensors macs to the sensor list
                                    sensors_list.Clear();
                                    for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                                        sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);
                                    
                                    //Update status message
                                    UpdateMsg("Wockets Swapped");
                                    Thread.Sleep(1000);
                                    Logger.Debug("Finish loading new set from Xml, new set: " + sensor_set);


                                    //--- Initialize Kernel  ---
                                    ResetACsCounters(wockets_controller);
                                    for (int i = 0; i < wockets_controller._Receivers.Count; i++)
                                    {
                                        PrevFullPkg[i] = 0;
                                        PrevPartialPkg[i] = 0;
                                        PrevEmptyPkg[i] = 0;
                                    }
                                   

                                    //Restart kernel (commented for now
                                    //SuscribeToKernelEvents();
                                    //Start the kernel connection sequence
                                    //StartLoadingWocketsToKernel();
                                    //Update status message
                                    //UpdateMsg("Kernel Started");
                                    //Thread.Sleep(1000);

                                    UpdateMsg("Verify Wockets");
                                    Core.SetSensors(this.sensors_list);
                                    Thread.Sleep(2000);
                                    Logger.Debug("Set Sensors Command Sent");

                                }
                                catch
                                {
                                    Logger.Debug("Swap sequence after wockets disconnected failed.");
                                }

                                    #endregion


                                break;

                            default:
                                break;
                        }

                    }
                }
                catch
                {
                    //Logger: exception in the event listener
                }
            }

       #endregion 



      #region Kernel Message Callback

        delegate void UpdateMsgCallback(string msg);
        private void UpdateMsg(string msg)
            {
            try
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateMsgCallback d = new UpdateMsgCallback(UpdateMsg);
                    this.Invoke(d, new object[] { msg });
                }
                else
                {   label_kernel_status.Text = msg;
                    Application.DoEvents();
                }

            }
            catch
            {
            }
        }


        //TODO: check how often this function is used
        delegate void UpdateSensorStatusCallback(string status_msg);
        private void UpdateSensorStatus(string status_msg)
        {
            try
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateSensorStatusCallback d = new UpdateSensorStatusCallback(UpdateSensorStatus);
                    this.Invoke(d, new object[] { status_msg });
                }
                else
                {
 
                    if (status_msg.CompareTo("Connected") == 0)
                    {
                        textBox_sensors_status.Text = "Kernel Connected";
                        textBox_sensors_status.ForeColor = Color.Green;

                        //update the sensor status panel
                        textBox_spanel_sensors_status.Text = "Kernel Connected";
                        textBox_spanel_sensors_status.ForeColor = Color.Green;

                        //update fields in main app actions panel
                        textBox_main_sensor_status.Text = "Kernel Connected";
                        textBox_main_sensor_status.ForeColor = Color.Green;
                    }
                    else if (status_msg.CompareTo("Disconnected") == 0)
                    {
                        textBox_sensors_status.Text = "Kernel Disconnected";
                        textBox_sensors_status.ForeColor = Color.DimGray;

                        //update the sensor status panel
                        textBox_spanel_sensors_status.Text = "Kernel Disconnected";
                        textBox_spanel_sensors_status.ForeColor = Color.DimGray;

                        //update fields in main app actions panel
                        textBox_main_sensor_status.Text = "Kernel Disconnected";
                        textBox_main_sensor_status.ForeColor = Color.DimGray;
                    }
                    else
                    {
                        textBox_sensors_status.Text = status_msg;
                        textBox_sensors_status.ForeColor = Color.DimGray;

                        //update the sensor status panel
                        textBox_spanel_sensors_status.Text = status_msg;
                        textBox_spanel_sensors_status.ForeColor = Color.DimGray;

                        //update fields in main app actions panel
                        textBox_main_sensor_status.Text = status_msg;
                        textBox_main_sensor_status.ForeColor = Color.DimGray;
                    }

                    Application.DoEvents();
                }
            }
            catch
            { 
                //Fail updating the sensors connection status
            }
        }

      #endregion 

      


      #endregion



      #region Exit/Connect Button (From Main Menu Bar)

        private void menuQuitApp_Click(object sender, EventArgs e)
        {

            if (menuQuitApp.Text.CompareTo("Quit") == 0)
            {
                menuQuitApp.Enabled = false;
                menuMainAppActions.Enabled = false;
                Logger.Debug("Quit Button Clicked");

                #region Exit Application

                #region Check which panel is open

                    string panel_open = "";

                    //Hide the swap panel
                    if (SwapPanel.Visible)
                    {
                        SwapPanel.Visible = false;
                        SwapPanel.Enabled = false;
                        panel_open = "Swap";
                    }
                    //Hide the main actions panel
                    else if (MainActionsPanel.Visible)
                    {
                        MainActionsPanel.Visible = false;
                        MainActionsPanel.Enabled = false;
                        panel_open = "Main";
                    }
                    //Hide the upload panel
                    else if (UploadDataPanel.Visible)
                    {
                        UploadDataPanel.Visible = false;
                        UploadDataPanel.Enabled = false;
                        panel_open = "Upload";
                    }
                    //Hide the sensors status panel
                    else if (SensorStatusPanel.Visible)
                    {
                        SensorStatusPanel.Visible = false;
                        SensorStatusPanel.Enabled = false;
                        panel_open = "Status";
                    }

                #endregion


                //Show the connect status panel
                label_kernel_status.Text = "...";
                ConnectPanel.BringToFront();
                ConnectPanel.Visible = true;
                ConnectPanel.Enabled = true;

                Application.DoEvents();


                if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                {
                    label_kernel_status.Text = "Exiting Application";
                    Application.DoEvents();

                    Logger.Debug("user confirmed to quit the application");

                    try
                    {
                        //Indicate that application was terminated by the user
                        StreamWriter wr_status = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_status.txt");
                        wr_status.WriteLine("normal_start");
                        wr_status.Flush();
                        wr_status.Close();
                    }
                    catch
                    {
                        Logger.Debug("An exception occurred when saving app status to file.");
                    }

                    TerminateApp();


                }
                else
                {
                    //Hide the connect panel
                    ConnectPanel.Visible = false;
                    ConnectPanel.Enabled = false;


                    #region Show the panel that was originally open

                    switch (panel_open)
                    {
                        case "Swap":
                            SwapPanel.BringToFront();
                            SwapPanel.Visible = true;
                            SwapPanel.Enabled = true;
                            break;
                        case "Main":
                            MainActionsPanel.BringToFront();
                            MainActionsPanel.Visible = true;
                            MainActionsPanel.Enabled = true;
                            break;
                        case "Upload":
                            UploadDataPanel.BringToFront();
                            UploadDataPanel.Visible = true;
                            UploadDataPanel.Enabled = true;
                            break;
                        case "Status":
                            SensorStatusPanel.BringToFront();
                            SensorStatusPanel.Visible = true;
                            SensorStatusPanel.Enabled = true;
                            break;

                        default:
                            break;
                    }

                    #endregion

                    Logger.Debug("User decided no to quit the application");
                }


                #endregion

                menuQuitApp.Enabled = true;
                menuMainAppActions.Enabled = true;
            }
            else if (menuQuitApp.Text.CompareTo("Connect") == 0)
            {
                menuQuitApp.Enabled = false;
                menuQuitApp.Text = "";
                Logger.Debug("User clicked the Connect button to start kernel in normal mode");

                #region Connect Application
                //Hide the swap panel
                SwapPanel.Enabled = false;
                SwapPanel.Visible = false;

                //Show the connect panel
                label_kernel_status.Text = "Load Wockets";
                ConnectPanel.BringToFront();
                ConnectPanel.Enabled = true;
                ConnectPanel.Visible = true;

                //Start the kernel connection sequence
                StartLoadingWocketsToKernel();
                
                Logger.Debug("Start loading wockets to kernel thread started");

                #endregion

                menuQuitApp.Text = "Quit";
                menuQuitApp.Enabled = true;

            }


        }

        public void TerminateApp()
        {
            try
            {
                Logger.Debug("Starting to quit application");

                //Launch status monitoring thread
                StopACsUpdater();

                //Wait for the system to stabilize and check that threads have finished
                Thread.Sleep(2000);

                //Terminate the kernel
                if (TerminateKernel()) //if (!Core._KernalStarted)
                {
                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
            }
            catch
            {
                Logger.Debug("An exception occurred when trying to quit the application");
            }
        }

        private bool TerminateKernel()
        {
            try
            {
                Logger.Debug("Initiating the kernel termination");
                Core.Unregister();
                return Core.Terminate();
            }
            catch
            { 
                Logger.Debug("An exception occurred when trying to terminate kernel");
                //Here try more agressive methods to stop the kernel
                return true;
            }
        }

      #endregion



      #region Minimize/Main Menu Button Actions

        private void menuMainAppActions_Click(object sender, EventArgs e)
        {

            try
            {
               
                if (menuMainAppActions.Text.CompareTo("Minimize") == 0)
                {
                    Minimize_Main_Window();
                    Logger.Debug("App was minimized");
                }
                else if (menuMainAppActions.Text.CompareTo("Main Menu") == 0)
                {
                    menuMainAppActions.Text = "Minimize";
                   
                    
                    #region Check which panel is open

                    //Hide the swap panel
                    if (SwapPanel.Visible)
                    {
                        SwapPanel.Visible = false;
                        SwapPanel.Enabled = false;
                    }
                    else if (UploadDataPanel.Visible)
                    {
                        UploadDataPanel.Visible = false;
                        UploadDataPanel.Enabled = false;
                        StopUpdateUploadThread();

                       //Hide the elapsed time label
                       textBox_elapsed_time.Visible = false;
                    }
                    else if (SensorStatusPanel.Visible)
                    {
                        SensorStatusPanel.Visible = false;
                        SensorStatusPanel.Enabled = false;
                    }

                    #endregion

                    //Show Main Actions Panel
                    MainActionsPanel.Visible = true;
                    MainActionsPanel.BringToFront();
                    MainActionsPanel.Enabled = true;

                    Logger.Debug("Go to the main menu panel");
                    
                }
            }
            catch(Exception ex) 
            {
                Logger.Debug("An exception occurred when minimizing/main menu button clicked");      
            }
        }

        private void Minimize_Main_Window()
        {
            ShowWindow(this.Handle, SW_MINIMIZED);
        }

    #endregion 

      
    
    #region Main Actions Panel Buttons

        private void SelectSensorsButton_Click(object sender, EventArgs e)
        {
            SelectSensorsButton.Enabled = false;
            Logger.Debug("Go to the Swap Panel");

            //Hide Connect Panel
            ConnectPanel.Visible = false;
            ConnectPanel.Enabled = false;

            //Hide Main Actions Panel
            MainActionsPanel.Visible = false;
            MainActionsPanel.Enabled = false;

            //Update Main App Actions Menu
            menuMainAppActions.Text = "Main Menu";

            //Show Swap Panel
            SwapPanel.BringToFront();
            SwapPanel.Visible = true;
            SwapPanel.Enabled = true;

            SelectSensorsButton.Enabled = true;

        }

        private void UploadDataActionButton_Click(object sender, EventArgs e)
        {
            UploadDataActionButton.Enabled = false;
            Logger.Debug("Go to the upload panel");

            //Hide Connect Panel
            ConnectPanel.Visible = false;
            ConnectPanel.Enabled = false;

            //Hide Main Actions Panel
            MainActionsPanel.Visible = false;
            MainActionsPanel.Enabled = false;

            //Hide Swap Panel
            SwapPanel.Visible = false;
            SwapPanel.Enabled = false;

            //Update Main App Actions Menu
            menuMainAppActions.Text = "Main Menu";

            //Show elapsed time timer label
            textBox_elapsed_time.Visible = true;
            
            //Show Upload Panel
            UploadDataPanel.BringToFront();
            UploadDataPanel.Visible = true;
            UploadDataPanel.Enabled = true;

            //Launch the update upload and timer thread
            StartUpdateUploadThread();

            UploadDataActionButton.Enabled = true;

        }

        private void SensorsStatusButton_Click(object sender, EventArgs e)
        {
            SensorsStatusButton.Enabled = false;
            Logger.Debug("Go to the sensor status panel");

            //Hide Connect Panel
            ConnectPanel.Visible = false;
            ConnectPanel.Enabled = false;

            //Hide Main Actions Panel
            MainActionsPanel.Visible = false;
            MainActionsPanel.Enabled = false;

            //Hide Swap Panel
            SwapPanel.Visible = false;
            SwapPanel.Enabled = false;

            //Update Main App Actions Menu
            menuMainAppActions.Text = "Main Menu";

            //Show Sensor Status Panel
            SensorStatusPanel.BringToFront();
            SensorStatusPanel.Visible = true;
            SensorStatusPanel.Enabled = true;

            #region commented
            //Load ACs To Kernel
            //Core.READ_EMPTY_RECEIVED_COUNT();
            //Core.READ_FULL_RECEIVED_COUNT();
            //Core.READ_PARTIAL_RECEIVED_COUNT();
            //TODO: Launch the thread to read sensors ACs
            //StartACsUpdater();
            #endregion

            SensorsStatusButton.Enabled = true;

        }

    #endregion

      
    #region Upload Data
        
        //Upload Button From UploadDataPanel
        private void UploadButton_Click(object sender, EventArgs e)
        {
            UploadButton.Enabled = false;
            Logger.Debug("upload data button clicked");

           try
           {        
                    //uploadCounter = 0;
                    prevFailed = prevSuccessful = -1;
                 
                    //Launch the uploader process
                    ProcessStartInfo startInfo = new ProcessStartInfo();
                    startInfo.WorkingDirectory = Core.KERNEL_PATH + "wocketsuploader\\";
                    startInfo.FileName = Core.KERNEL_PATH + "wocketsuploader\\" + "DataUploader.exe";
                    startInfo.UseShellExecute = false;
                    _UploaderProcess = System.Diagnostics.Process.Start(startInfo.FileName, "");

                    //update status
                    if (_UploaderProcess != null)
                    {
                        label_upload_data_status.Text = "Uploading Data";
                        label_upload_data_status.ForeColor = Color.Green;
                    }
                    else
                    {
                        label_upload_data_status.Text = "upload process couldn't start";
                        label_upload_data_status.ForeColor = Color.DimGray;
                        UploadButton.Enabled = true;
                    }

                   //TODO: Add an asynchronous sleep here
            }
           catch(Exception ex)
            {
                UploadButton.Enabled = true;
                Logger.Debug("An exception occureed when trying to launch the uploader.exe program");
           }
        }

    #endregion


    #region Elapsed Time Counter & Upload Thread
      
      public void StartUpdateUploadThread()
      {
          //Start Timer Thread
          uploadThread = new Thread(new ThreadStart(RunUploadThread));
          uploadThread.Start();
      }

      public void StopUpdateUploadThread()
      {
          if (uploadThread != null)
          { uploadThread.Abort();
            Logger.Debug("upload monitor thread stopped");
          }
      }

      private void RunUploadThread()
      {
          Logger.Debug("upload monitor thread started");

          try
          {
              while (true)
              {
                  //TODO: Compute Elapsed Time
                  TimeSpan elapsed_duration = DateTime.Now.Subtract(Settings._SessionStart);

                  if (elapsed_duration.Days > 0)
                      ElapsedTime = elapsed_duration.Days.ToString("00") + "days  " + elapsed_duration.Hours.ToString("00") + "h:" + elapsed_duration.Minutes.ToString("00") + "m:" + elapsed_duration.Seconds.ToString("00") + "s";
                  else
                      ElapsedTime = elapsed_duration.Hours.ToString("00") + "h:" + elapsed_duration.Minutes.ToString("00") + "m:" + elapsed_duration.Seconds.ToString("00") + "s";


                  UpdateFilesUploaded();
                  Thread.Sleep(500);
              }
          }
          catch
          {
              Logger.Debug("An exception occurred when trying to update the file upload parameters");
          }
      }

   #endregion


   #region Update Callback

      delegate void UpdateTimeCallback();
      public void UpdateFilesUploaded()
      {
          if (!disposed)
          {
              if (textBox_elapsed_time.InvokeRequired)
              // InvokeRequired required compares the thread ID of the
              // calling thread to the thread ID of the creating thread.
              // If these threads are different, it returns true.
              {
                  UpdateTimeCallback d = new UpdateTimeCallback(UpdateFilesUploaded);
                  this.Invoke(d, new object[] { });
              }
              else
              {
                  //TODO: Duration Label
                  textBox_elapsed_time.Text = ElapsedTime;

                  counter++;

                  if (counter == 5)
                  {
                      //Update the upload files fields
                      Core.READ_LAST_UPLOAD_DURATION();
                      Core.READ_LAST_UPLOAD_FAILEDFILES();
                      Core.READ_LAST_UPLOAD_NEWFILES();
                      Core.READ_LAST_UPLOAD_SUCCESSFILES();
                      Core.READ_LAST_UPLOAD_TIME();


                      //update new files label
                      textBox_uploader_new_files.Text = CurrentWockets._UploadNewFiles.ToString();


                      #region Compute elapsed time since last upload
                      

                      if (CurrentWockets._UploadLastTime.Year != 1961)
                      {
                          TimeSpan duration = DateTime.Now.Subtract(CurrentWockets._UploadLastTime);

                          //update the status of the last file upload
                          if (duration.TotalDays >= 2)
                              this.textBox_updater_last_update.Text = ((int)duration.TotalDays).ToString() + " days ago";
                          else if (duration.TotalHours > 2)
                              this.textBox_updater_last_update.Text = ((int)duration.TotalHours) + " hours ago";
                          else
                              this.textBox_updater_last_update.Text = ((int)duration.TotalMinutes) + " mins ago";
                      }
                      else
                      {
                          //update the status fields of the data time duration
                          this.textBox_updater_last_update.Text = "never";
                      }


                      #endregion


                      //update the upload status indicators
                      textBox_uploader_duration.Text = CurrentWockets._UploadDuration;
                      textBox_uploader_successful_files.Text = CurrentWockets._UploadSuccessFiles.ToString();
                      textBox_uploader_failed_files.Text = CurrentWockets._UploadFailedFiles.ToString();

                      //If finished uploading, reset counter
                      //if ((prevSuccessful != CurrentWockets._UploadSuccessFiles) ||
                      //    (prevFailed != CurrentWockets._UploadFailedFiles))
                      //    uploadCounter = 0;

                      //update counters
                      prevSuccessful = CurrentWockets._UploadSuccessFiles;
                      prevFailed = CurrentWockets._UploadFailedFiles;

                      counter = 0;


                      #region Determine if the uploader program is still running
                      try
                      {
                          ProcessInfo[] processes = ProcessCE.GetProcesses();

                          if (processes != null)
                          {
                              bool found = false;
                              for (int i = 0; (i < processes.Length); i++)
                              {
                                  if (processes[i].FullPath.IndexOf("DataUploader.exe") >= 0)
                                  {
                                      found = true;
                                      break;
                                  }
                              }

                              //update status
                              if (found)
                              {
                                  label_upload_data_status.Text = "uploading data";
                                  label_upload_data_status.ForeColor = Color.Green;
                                  this.UploadButton.Enabled = false;
                              }
                              else
                              {
                                  label_upload_data_status.Text = "...";
                                  label_upload_data_status.ForeColor = Color.DimGray;
                                  this.UploadButton.Enabled = true;
                              }    

                          }
                      }
                      catch (Exception e){ }

                      #endregion


                      if (_UploaderProcess == null)
                      {
                          label_upload_data_status.Text = "...";
                          label_upload_data_status.ForeColor = Color.DimGray;
                          this.UploadButton.Enabled = true;
                      }
                      else if ((!this.UploadButton.Enabled) && ((_UploaderProcess != null) && (_UploaderProcess.HasExited)))
                      {
                          label_upload_data_status.Text = "...";
                          label_upload_data_status.ForeColor = Color.DimGray;
                          this.UploadButton.Enabled = true;
                      }
                  }

                  this.Invalidate();
              }
          }
      }

    #endregion



    #region Read ACs for Sensor Status

     private void ResetACsCounters(WocketsController wc)
      {
          try
          {
              for (int i = 0; (i < wc._Receivers.Count); i++)
              {
                  Core.WRITE_FULL_RECEIVED_COUNT(i, 0);
                  Core.WRITE_PARTIAL_RECEIVED_COUNT(i, 0);
                  Core.WRITE_EMPTY_RECEIVED_COUNT(i, 0);
                  Core.WRITE_RECEIVED_ACs(i, -1);
                  Core.WRITE_SAVED_ACs(i, -1);
              }
          }
          catch
          {
              Logger.Debug("An exception occurred when trying to reset ACs counters");
          }
      }



     
     

     
     void ACsUpdateTimer_Tick(object sender, EventArgs e)
     {
         bool received_count_read = false;

         try
         {
             if (CurrentWockets._Controller._Sensors != null)
             {
                 if (CurrentWockets._Controller._Sensors.Count > 0)
                 {

                     for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
                     {

                         //== Compute the elapsed time since the last connection
                         ElapsedConnectionTime[i] = DateTime.Now.Subtract(LastPkgTime[i]);

                         //if et>1min check pkg status
                         if (ElapsedConnectionTime[i].TotalMinutes > 1.0)
                         {

                             #region IF ELAPSED TIME > 1MIN


                             #region Load the AC Counts to Kernel

                             if (!received_count_read)
                             {
                                 Core.READ_EMPTY_RECEIVED_COUNT();
                                 Core.READ_FULL_RECEIVED_COUNT();
                                 Core.READ_PARTIAL_RECEIVED_COUNT();
                                 Core.READ_RECEIVED_ACs();
                                 Core.READ_SAVED_ACs();

                                 received_count_read = true;
                             }

                             #endregion


                             #region Update the ACs on the Screen

                             if (i == 0)
                             {
                                 this.textBox_spanel_ac_full_0.Text = CurrentWockets._Controller._Sensors[_ID]._Full.ToString();
                                 this.textBox_spanel_ac_partial_0.Text = CurrentWockets._Controller._Sensors[i]._Partial.ToString();
                                 this.textBox_spanel_ac_empty_0.Text = CurrentWockets._Controller._Sensors[i]._Empty.ToString();

                                 this.textBox_spanel_ac_new_0.Text = CurrentWockets._Controller._Sensors[i]._SavedACs + " - " + CurrentWockets._Controller._Sensors[i]._TotalSavedACs;
                                 this.textBox_spanel_ac_last_0.Text = CurrentWockets._Controller._Sensors[i]._ReceivedACs + " - " + CurrentWockets._Controller._Sensors[i]._TotalReceivedACs;
                             }
                             else
                             {
                                 this.textBox_spanel_ac_full_1.Text = CurrentWockets._Controller._Sensors[i]._Full.ToString();
                                 this.textBox_spanel_ac_partial_1.Text = CurrentWockets._Controller._Sensors[i]._Partial.ToString();
                                 this.textBox_spanel_ac_empty_1.Text = CurrentWockets._Controller._Sensors[i]._Empty.ToString();

                                 this.textBox_spanel_ac_new_1.Text = CurrentWockets._Controller._Sensors[i]._SavedACs + " - " + CurrentWockets._Controller._Sensors[i]._TotalSavedACs;
                                 this.textBox_spanel_ac_last_1.Text = CurrentWockets._Controller._Sensors[i]._ReceivedACs + " - " + CurrentWockets._Controller._Sensors[i]._TotalReceivedACs;
                             }

                             #endregion



                             //If Full/Partial Packages Changed
                             if (CurrentWockets._Controller._Sensors[i]._Full > PrevFullPkg[i] ||
                                  CurrentWockets._Controller._Sensors[i]._Partial > PrevPartialPkg[i])
                             {

                                 #region Update Fields

                                 PrevFullPkg[i] = CurrentWockets._Controller._Sensors[i]._Full;
                                 PrevPartialPkg[i] = CurrentWockets._Controller._Sensors[i]._Partial;

                                 if (i == 0)
                                 {
                                     textBox_sensors_status_0.Text = "Saving Data";
                                     textBox_sensors_status_0.ForeColor = Color.Orange;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_1.Text = "Saving Data";
                                     textBox_sensors_status_1.ForeColor = Color.Orange;
                                 }

                                 LastPkgTime[i] = DateTime.Now;

                                 #endregion

                             }
                             //If Empty Packages Changed
                             else if (CurrentWockets._Controller._Sensors[i]._Empty > PrevEmptyPkg[i])
                             {

                                 #region Update Fields

                                 PrevEmptyPkg[i] = CurrentWockets._Controller._Sensors[i]._Empty;

                                 if (i == 0)
                                 {
                                     textBox_sensors_status_0.Text = "Data Lost";
                                     textBox_sensors_status_0.ForeColor = Color.Tomato;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_1.Text = "Data Lost";
                                     textBox_sensors_status_1.ForeColor = Color.Tomato;
                                 }

                                 #endregion

                             }
                             //If the # of packages didn't changed
                             else
                             {

                                 #region Update Fields

                                 if (ElapsedConnectionTime[i].TotalMinutes <= 5.0)
                                 {
                                     if (i == 0)
                                     {
                                         textBox_sensors_status_0.Text = "Waiting For Data";
                                         textBox_sensors_status_0.ForeColor = Color.DimGray;
                                     }
                                     else
                                     {
                                         textBox_sensors_status_1.Text = "Waiting For Data";
                                         textBox_sensors_status_1.ForeColor = Color.DimGray;
                                     }
                                 }
                                 else
                                 {
                                     if (i == 0)
                                     {
                                         textBox_sensors_status_0.Text = "No Data Received";
                                         textBox_sensors_status_0.ForeColor = Color.Red;
                                     }
                                     else
                                     {
                                         textBox_sensors_status_1.Text = "No Data Received";
                                         textBox_sensors_status_1.ForeColor = Color.Red;
                                     }
                                 }

                                 #endregion

                             }


                             #endregion

                         }
                         else
                         {

                             #region IF ELAPSED TIME < 1min

                             //If Full/Partial Packages == 0 never received data                     
                             if (CurrentWockets._Controller._Sensors[i]._Full == 0 &
                                 CurrentWockets._Controller._Sensors[i]._Partial == 0)
                             {
                                 if (i == 0)
                                 {
                                     textBox_sensors_status_0.Text = "---";
                                     textBox_sensors_status_0.ForeColor = Color.DimGray;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_1.Text = "---";
                                     textBox_sensors_status_1.ForeColor = Color.DimGray;
                                 }
                             }
                             else
                             {
                                 if (i == 0)
                                 {
                                     textBox_sensors_status_0.Text = "Data Received";
                                     textBox_sensors_status_0.ForeColor = Color.Green;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_1.Text = "Data Received";
                                     textBox_sensors_status_1.ForeColor = Color.Green;
                                 }
                             }

                             #endregion

                         }

                     }//ends for loop

                 }//if sensors count >0
             }//if sensors list != null
         }
         catch
         {
             Logger.Debug("An exeption occurred when updating/monitoring the Acs counts for connection status");
         }

     }


        public void StartACsUpdater()
        {
            ACsUpdateTimer.Enabled = true;
        }

        public void StopACsUpdater()
        {
            ACsUpdateTimer.Enabled = false;
        }



        #region Update ACs Event Listener

        //delegate void UpdateACsCallback();
        //private void UpdateACsEventListener()
        //{
        //    try
        //    {
        //        Core.READ_EMPTY_RECEIVED_COUNT();
        //        Core.READ_FULL_RECEIVED_COUNT();
        //        Core.READ_PARTIAL_RECEIVED_COUNT();
        //        Core.READ_RECEIVED_ACs();
        //        Core.READ_SAVED_ACs();


        //        // InvokeRequired required compares the thread ID of the
        //        // calling thread to the thread ID of the creating thread.
        //        // If these threads are different, it returns true.
        //        if (this.InvokeRequired || this.InvokeRequired)
        //        {
        //            UpdateACsCallback d = new UpdateACsCallback(UpdateACsEventListener);
        //            this.Invoke(d, new object[] { });
        //        }
        //        else
        //        {


        //            //Update the ACs For Sensor ID=0 on the Screen
        //            _ID = 0;
        //            this.textBox_spanel_ac_full_0.Text = CurrentWockets._Controller._Sensors[_ID]._Full.ToString();
        //            this.textBox_spanel_ac_partial_0.Text = CurrentWockets._Controller._Sensors[_ID]._Partial.ToString();
        //            this.textBox_spanel_ac_empty_0.Text = CurrentWockets._Controller._Sensors[_ID]._Empty.ToString();

        //            this.textBox_spanel_ac_new_0.Text = CurrentWockets._Controller._Sensors[_ID]._SavedACs + " - " + CurrentWockets._Controller._Sensors[_ID]._TotalSavedACs;
        //            this.textBox_spanel_ac_last_0.Text = CurrentWockets._Controller._Sensors[_ID]._ReceivedACs + " - " + CurrentWockets._Controller._Sensors[_ID]._TotalReceivedACs;


        //            //Update the ACs For Sensor ID=1 on the Screen
        //            _ID = 1;
        //            this.textBox_spanel_ac_full_1.Text = CurrentWockets._Controller._Sensors[_ID]._Full.ToString();
        //            this.textBox_spanel_ac_partial_1.Text = CurrentWockets._Controller._Sensors[_ID]._Partial.ToString();
        //            this.textBox_spanel_ac_empty_1.Text = CurrentWockets._Controller._Sensors[_ID]._Empty.ToString();

        //            this.textBox_spanel_ac_new_1.Text = CurrentWockets._Controller._Sensors[_ID]._SavedACs + " - " + CurrentWockets._Controller._Sensors[_ID]._TotalSavedACs;
        //            this.textBox_spanel_ac_last_1.Text = CurrentWockets._Controller._Sensors[_ID]._ReceivedACs + " - " + CurrentWockets._Controller._Sensors[_ID]._TotalReceivedACs;



        //            this.Invalidate();

        //        }
        //    }
        //    catch (Exception e)
        //    {
        //    }

        //}

        #endregion


      #endregion



    }



    #region Internal Message Window
    
    #region Description
    //This window receives messages from another program (in this case the updater).
    //The message is identified and decoded. 
    //If the "TERMINATE" message is sent, the window closes the kernel.
    #endregion

    internal class internalMessageWindow : MessageWindow
    {
        WocketsMainForm referedForm;
        private const int TERMINATE_MESSAGE = 0xA123;


        public internalMessageWindow(WocketsMainForm referedForm)
        {
            this.referedForm = referedForm;
            this.Text = "WocketsMessageWindow";
        }


        protected override void WndProc(ref Message m)
        {

            //filter the Terminate Message
            if (m.Msg == TERMINATE_MESSAGE)
            {
                referedForm.TerminateApp();
            }

            //make sure to pass along all messages
            base.WndProc(ref m);
        }


    }


    #endregion


}