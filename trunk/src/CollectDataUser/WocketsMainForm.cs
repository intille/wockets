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
using System.Runtime.InteropServices; //For Dll Imports
using System.Diagnostics; //Processes related functions
using Microsoft.WindowsCE.Forms; //For the hidden communication window

using Wockets;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets.Data.Types;
using Wockets.Receivers;
using Wockets.Utils;
using Wockets.Utils.IPC;
using Wockets.Utils.feedback;


namespace CollectDataUser
{

    enum PanelID 
    {
        MAIN,
        SWAP,
        UPLOAD,
        STATUS,
        CONNECTION
    }

    enum MasterListParam
    {
        IMEI,               //phone ID
        Set1_ID,            //set color
        Set1_ForceUpdate,   //yes, no
        Set1_MAC_Acc0,      //mac sensor 0
        Set1_MAC_Acc1,      //mac sensor 1
        Set2_ID,
        Set2_ForceUpdate,
        Set2_MAC_Acc0,
        Set2_MAC_Acc1      
    }



    public partial class WocketsMainForm : Form
    {


      #region Variables

        //General Status Variables
        private String sensor_set = "";
        private String app_status = "";
        private String software_version = "";
        private bool is_rebooting = false;

        //Wockets Controller
        private WocketsController wockets_controller = null; 
        private Thread startupThread = null;    //starts kernel and load wockets
        private ArrayList sensors_list = null;
        private string[] sensor_data = null;


        //Data Uploader
        private Thread uploadThread;
        private static System.Diagnostics.Process _UploaderProcess = null;
        private static System.Diagnostics.Process _LogUploaderProcess = null;

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

        private DateTime LastLogUploadInvoke;
        private TimeSpan ElapsedTime_LogUpload;

        //private DateTime LastDataUploadInvoke;
        private TimeSpan ElapsedTime_DataUpload;
        

        
        #endregion 


        private static IntPtr handle_blt = IntPtr.Zero;

        public enum CEDEVICE_POWER_STATE
        {
            PwrDeviceUnspecified = -1,
            D0 = 0,  // on
            D1,      // low power
            D2,      // standby, system cannot wakeup the system
            D3,      // sleep, device can wakeup the system
            D4,      // off
            PwrDeviceMaximum
        }

        public enum PowerStateRequirement
        {
            POWER_NAME = 0x00000001,         // default
            POWER_FORCE = 0x00001000,
            POWER_DUMPDW = 0x00002000        // Calling CaptureDumpFileOnDevice() before entering this state.
        }


        public enum PowerState
        {
            POWER_STATE_ON = 0x00010000,         // power state in P3600
            POWER_STATE_OFF = 0x00020000,
            POWER_STATE_CRITICAL = 0x00040000,
            POWER_STATE_BOOT = 0x00080000,
            POWER_STATE_IDLE = 0x00100000,         //---> screen off,  touch disabled
            POWER_STATE_SUSPEND = 0x00200000,
            POWER_STATE_UNATTENDED = 0x00400000,
            POWER_STATE_RESET = 0x00800000,
            POWER_STATE_USERIDLE = 0x01000000,     //---> user idle, screen off, but touch enabled
            POWER_STATE_PASSWORD = 0x10000000,     //---> resuming
            POWER_STATE_BACKLIGHTOFF = 0x10010000, //---> bkl-off
            POWER_STATE_POWERON = 0x12010000       // power state in P3300
        }


        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int SetDevicePower(string psDevice, PowerStateRequirement dflags, CEDEVICE_POWER_STATE device_state);

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int SetSystemPowerState(string psState, PowerState stateflags, int options);


      #region Initialize Form


        public WocketsMainForm()
        {

            is_rebooting = false;

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
        


            #region Read the Sowftware Version

            System.Reflection.Assembly a = System.Reflection.Assembly.GetExecutingAssembly();
            System.Reflection.AssemblyName an = a.GetName();
            software_version = "Version: " + an.Version.ToString();
            this.label_software_version.Text = software_version.Substring(0, 14);


            #endregion


            #region Read Phone IMEI

            label_phone_IMEI.Text = CurrentPhone._IMEI;

            #endregion


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

           
            #region Read the last sensor set, kernel status, and master list files



            #region Read the last kernel status


            try
            {
                if (File.Exists(Core.KERNEL_PATH + "\\updater_last_status.txt"))
                {
                    StreamReader tr_status = new StreamReader(Core.KERNEL_PATH + "\\updater_last_status.txt");

            try
            {
                if (File.Exists(Core.KERNEL_PATH + "\\updater_last_status.txt"))
                {
                    StreamReader tr_status = new StreamReader(Core.KERNEL_PATH + "\\updater_last_status.txt");
                    
                    app_status = tr_status.ReadLine();
                    string vibrate_mode = tr_status.ReadLine();
                    string mute_mode    = tr_status.ReadLine();
                    string volume_mode = tr_status.ReadLine();
                    #region commented
                    //string vibrate_mode = tr_status.ReadLine();
                    //string mute_mode = tr_status.ReadLine();
                    //string volume_mode = tr_status.ReadLine();
                    #endregion 

                    tr_status.Close();


                    if (this.app_status.CompareTo("") == 0)
                    { this.app_status = "normal_start"; }
                }

            }
            catch
            {
                this.app_status = "normal_start";
            }


                    tr_status.Close();


                    if (this.app_status.CompareTo("") == 0)
                    { this.app_status = "normal_start"; }


                    //if (vibrate_mode != null && vibrate_mode.CompareTo("vibrate") == 0)
                    //    SetProfileVibrate();
                    //else if ( mute_mode!= null && mute_mode.CompareTo("muted") == 0)
                    //    SetProfileMuted();
                    //else

                    //waveOutSetVolume(IntPtr.Zero, (int)Volumes.MEDIUM);

                    //SetProfileNormal(SND_EVENT.RingLine1);
                    //SetProfileNormal(SND_EVENT.KnownCallerLine1);

                    //if (this.app_status.CompareTo("normal_start") != 0)
                    //{
                        //DisplayPower.PowerOff();
                        //SetDevicePower("BKL1:", PowerStateRequirement.POWER_NAME, CEDEVICE_POWER_STATE.D4);
                        SetSystemPowerState(null, PowerState.POWER_STATE_USERIDLE, 0);
                    //}
                }
                else
                {
                    //set the app to start from beginning
                    this.app_status = "normal_start";

                    //set audio settings to normal
                    //SetProfileNormal(SND_EVENT.All);
                    //waveOutSetVolume(IntPtr.Zero, (int)Volumes.MEDIUM);

                }
            }
            catch
            {
                this.app_status = "normal_start";
            }

            #endregion


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

            #region Read Master List File


            try
            {
                if (File.Exists(Core.KERNEL_PATH + "\\MasterList.txt"))
                {

                    StreamReader tr_sensors_data = new StreamReader(Core.KERNEL_PATH + "\\MasterList.txt");
                    string rline = tr_sensors_data.ReadLine();
                    bool is_IMEI_found = false;

                    while( rline != null & is_IMEI_found== false)
                    {
                        sensor_data = rline.Split(',');
                        if (sensor_data != null & sensor_data.Length == 9)
                        {
                            if (sensor_data[0].CompareTo(CurrentPhone._IMEI) == 0)
                                is_IMEI_found = true;
                        }
                        else
                            sensor_data = null;

                        rline = tr_sensors_data.ReadLine(); 
                    }

                    tr_sensors_data.Close();

                    if (!is_IMEI_found)
                        Logger.Debug("User IMEI not found in master list.");


                }
            }
            catch

            {
                Logger.Debug("sensor master file couldn't be accessed correctly.");
            }


            #endregion


            #endregion

            
            #region Check updates from master list


            #region Check MAC addresses updates from master list


            wockets_controller = new Wockets.WocketsController("", "", "");

            LoadSensorsFromMasterList(wockets_controller, sensor_data, this.sensor_set);

            // point kernel to wockets controller
            CurrentWockets._Controller = wockets_controller;

            //Load sensors addresses to array list
            sensors_list = new ArrayList();
            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);

            Logger.Debug("Sensor Info Loaded From Xml, Sensor Set: " + sensor_set + "," + "MACS:" +
                          sensors_list[0] + "," + sensors_list[1]);


            #endregion



            #region Suscribe to Kernel Events


            SuscribeToKernelEvents();




            #region Initialize thread that tracks the connection status


            ACsUpdateTimer = new System.Windows.Forms.Timer();
            ACsUpdateTimer.Interval = 1000;
            ACsUpdateTimer.Tick += new EventHandler(ACsUpdateTimer_Tick);
            ACsUpdateTimer.Enabled = false;



            #region Initialization of Connection Status Variables

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


            ElapsedTime_LogUpload = TimeSpan.Zero;
            LastLogUploadInvoke = new DateTime();
            LastLogUploadInvoke = DateTime.Now;
            ElapsedTime_DataUpload = TimeSpan.Zero;

            #endregion


            #endregion

           
            #region Initialize Elapsed Time Counter On File Upload Screen

            //Hide the timer label
            textBox_elapsed_time.Visible = false;
            textBox_elapsed_time.Text = "00h:00m:00s";

            #endregion
 

            #region Try to connect to kernel, using the loaded settings

            #region Initialize GUI Panels

            InitializePanels();

            #endregion


            if (app_status.CompareTo("normal_start") == 0)
            {

                //Setup the main menu commands
                menuMainAppActions.Text = "Main Menu";
                
                //menuQuitApp.Text = "Connect";
                menuQuitApp.Text = "Quit";

                #region Hide the connect panel (commented)
                //ConnectPanel.Enabled = false;
                //ConnectPanel.Visible = false;

                ////Hide the Main Actions Buttons Panel
                //MainActionsPanel.Visible = false;
                //MainActionsPanel.Enabled = false;

                ////Hide the Sensor Status Panel
                //SensorStatusPanel.Visible = false;
                //SensorStatusPanel.Enabled = false;
                
                ////Show the swap panel
                //SwapPanel.BringToFront();
                //SwapPanel.Enabled = true;
                //SwapPanel.Visible = true;
                #endregion

                TurnOnPanel(PanelID.SWAP);

                //update the sensor set/swap panel
                Show_Swap_Panel("Disconnected", sensor_set, CurrentWockets._Controller);
                Logger.Debug("Connecting to Kernel in Normal Mode");

            }
            else
            {
                #region Hide the swap panel
                //SwapPanel.Enabled = false;
                //SwapPanel.Visible = false;

                ////Hide the Main Actions Buttons Panel
                //MainActionsPanel.Visible = false;
                //MainActionsPanel.Enabled = false;

                ////Hide the Sensor Status Panel
                //SensorStatusPanel.Visible = false;
                //SensorStatusPanel.Enabled = false;

                ////Show the connect panel
                //ConnectPanel.BringToFront();
                //ConnectPanel.Enabled = true;
                //ConnectPanel.Visible = true;
                #endregion

                TurnOnPanel(PanelID.CONNECTION);
                label_kernel_status.Text = "";

                //Start the kernel connection sequence
                StartLoadingWocketsToKernel();
                Logger.Debug("Connecting to Kernel in Silent Mode");

            }

            #endregion


            #region Reset Uploader and Received Data Pkgs Counters

            ResetUploaderCounters();

            ResetACsCounters(wockets_controller);

            #endregion
      

        }


        #endregion


      #region Set Panels ON/OFF

        private PanelID LastPanel = PanelID.SWAP;
        private PanelID CurrentPanel = PanelID.SWAP;

        private void InitializePanels()
        {
            MainActionsPanel.Visible = false;
            MainActionsPanel.Enabled = false;

            SwapPanel.Visible = false;
            SwapPanel.Enabled = false;

            UploadDataPanel.Visible = false;
            UploadDataPanel.Enabled = false;

            SensorStatusPanel.Visible = false;
            SensorStatusPanel.Enabled = false;

            ConnectPanel.Visible = false;
            ConnectPanel.Enabled = false;

        }

        private void TurnOnPanel(PanelID ID)
        { 

            #region TurnOff CurrentPanel & Update LastPanelSet variable

           
            switch( CurrentPanel)
            {
                   case PanelID.SWAP:
                            SwapPanel.Visible = false;
                            SwapPanel.Enabled = false;
                            break;

                case PanelID.MAIN:
                            MainActionsPanel.Visible = false;
                            MainActionsPanel.Enabled = false;
                            break;
            
                case PanelID.UPLOAD:
                            UploadDataPanel.Visible = false;
                            UploadDataPanel.Enabled = false;
                            break;
            
                case PanelID.STATUS:
                            SensorStatusPanel.Visible = false;
                            SensorStatusPanel.Enabled = false;
                            break;

                case PanelID.CONNECTION:
                            ConnectPanel.Visible = false;
                            ConnectPanel.Enabled = false;
                            break;
                default :
                            break;
            }

            LastPanel = CurrentPanel;
              
            #endregion


            #region TurnOn Requested Panel & Update CurrentPanelSet variable

            switch (ID)
            {
                case PanelID.SWAP:
                    SwapPanel.BringToFront();
                    SwapPanel.Visible = true;
                    SwapPanel.Enabled = true;
                    break;

                case PanelID.MAIN:
                    MainActionsPanel.BringToFront();
                    MainActionsPanel.Visible = true;
                    MainActionsPanel.Enabled = true;
                    break;

                case PanelID.UPLOAD:
                    MainActionsPanel.BringToFront();
                    UploadDataPanel.Visible = true;
                    UploadDataPanel.Enabled = true;
                    break;

                case PanelID.STATUS:
                    SensorStatusPanel.BringToFront();
                    SensorStatusPanel.Visible = true;
                    SensorStatusPanel.Enabled = true;
                    break;

                case PanelID.CONNECTION:
                    ConnectPanel.BringToFront();
                    ConnectPanel.Visible = true;
                    ConnectPanel.Enabled = true;
                    break;
                default:
                    break;
            }

            CurrentPanel = ID;

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

            #region commented
            ////Hide the connect status panel
            //SwapPanel.Visible = false;
            //SwapPanel.Enabled = false;


            ////Show the connect status panel
            //ConnectPanel.BringToFront();
            //ConnectPanel.Visible = true;
            //ConnectPanel.Enabled = true;
            #endregion

            TurnOnPanel(PanelID.CONNECTION);

            try
            {
                if (app_status.CompareTo("running") == 0)
                {
                    //TODO: monitor the time that takes to receive the disconnect response
                    //      to avoid the operation hangs.

                    //Disconnect current sensors set from kernel
                    Core.Disconnect();
                    UpdateMsg("Disconnecting Wockets");
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

                    #region Hide the connect status panel
                    //ConnectPanel.Visible = false;
                    //ConnectPanel.Enabled = false;

                    ////Show the swap panel
                    //SwapPanel.BringToFront();
                    //SwapPanel.Visible = true;
                    //SwapPanel.Enabled = true;
                    #endregion

                    TurnOnPanel(PanelID.SWAP);

                    //Update the swap interface
                    Show_Swap_Panel("Disconnected", sensor_set, wockets_controller);

                }
            }
            catch
            {
                Logger.Debug("An exception ocurred when the swap button was clicked.");
            }

        }


        private void LoadSensorsFromMasterList(WocketsController wc, string[] loaded_sensor_data, string sensor_set_id)
        {
          
            if (loaded_sensor_data != null )
            {
                #region Determine the sensor set to be loaded & load it to the wockets receivers

               
                if (sensor_set_id.CompareTo(loaded_sensor_data[(int)MasterListParam.Set1_ID]) == 0)
                {
                    #region Load Sensor Set 1

                        // Open the Xml File containing the sensor parameters for Set 1
                        try
                            {   
                                if (File.Exists(Core.KERNEL_PATH + "\\updater_SensorData1.xml"))
                                    wc.FromXML(Core.KERNEL_PATH + "\\updater_SensorData1.xml");
                                else
                                    wc.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
                            }
                        catch
                            { Logger.Debug("The SensorData1.Xml couldn't be opened."); }


                        #region If the sensors are different from the ones in the master list, update the wockets controller settings
                        try
                        {
                            bool is_mac_changed = false;

                            if ((((RFCOMMReceiver)wc._Receivers[0])._Address.CompareTo(loaded_sensor_data[(int)MasterListParam.Set1_MAC_Acc0]) != 0))
                            {
                                //replace the mac address 
                                ((RFCOMMReceiver)wc._Receivers[0])._Address = loaded_sensor_data[(int)MasterListParam.Set1_MAC_Acc0];
                                is_mac_changed = true;

                                //TODO: send commands to get the sensor calibration values & effective sampling rate
                            }


                            if ((((RFCOMMReceiver)wc._Receivers[1])._Address.CompareTo(loaded_sensor_data[(int)MasterListParam.Set1_MAC_Acc1]) != 0))
                            {
                                //replace the mac address
                                ((RFCOMMReceiver)wc._Receivers[1])._Address = loaded_sensor_data[(int)MasterListParam.Set1_MAC_Acc1];
                                is_mac_changed = true;

                                //TODO:send commands to get the sensor calibration values & effective sampling rate
                            }


                            //Save the new sensor parameters to the Xml file
                            if (is_mac_changed)
                            {
                                StreamWriter sensors_data_xml = new StreamWriter(Core.KERNEL_PATH + "\\updater_SensorData1.xml");
                                sensors_data_xml.Write(wc.ToXML());
                                sensors_data_xml.Close();
                            }
                        }
                        catch(Exception e)
                        { 
                            Logger.Debug("An exeption occurred when trying to update macs with master list, set1. Ex: " + e); 
                        }

                    #endregion


                    #endregion

                }
                else
                {
                    #region Load SensorSet 2

                        //Open the Xml File containing the sensor parameters for Set 2
                        try
                        {
                            if (File.Exists(Core.KERNEL_PATH + "\\updater_SensorData2.xml"))
                                wc.FromXML(Core.KERNEL_PATH + "\\updater_SensorData2.xml");
                            else
                                wc.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");
                        }
                        catch
                        { Logger.Debug("The SensorData2.Xml couldn't be opened."); }


                        #region If the sensors are different from the ones in the master list, update the controller settings

                        try
                        {
                            bool is_mac_changed = false;

                            if ((((RFCOMMReceiver)wc._Receivers[0])._Address.CompareTo(loaded_sensor_data[(int)MasterListParam.Set2_MAC_Acc0]) != 0))
                            {
                                //replace the mac address 
                                ((RFCOMMReceiver)wc._Receivers[0])._Address = loaded_sensor_data[(int)MasterListParam.Set2_MAC_Acc0];
                                is_mac_changed = true;
                                //TODO: send commands to get the sensor calibration values & effective sampling rate
                            }


                            if ((((RFCOMMReceiver)wc._Receivers[1])._Address.CompareTo(loaded_sensor_data[(int)MasterListParam.Set2_MAC_Acc1]) != 0))
                            {
                                //replace the mac address
                                ((RFCOMMReceiver)wc._Receivers[1])._Address = loaded_sensor_data[(int)MasterListParam.Set2_MAC_Acc1];
                                is_mac_changed = true;
                                //send commands to get the sensor calibration values & effective sampling rate
                            }


                            //Save the new sensor parameters to the Xml file
                            if (is_mac_changed)
                            {
                                StreamWriter sensors_data_xml = new StreamWriter(Core.KERNEL_PATH + "\\updater_SensorData2.xml");
                                sensors_data_xml.Write(wc.ToXML());
                                sensors_data_xml.Close();
                            }

                        }
                        catch(Exception e)
                        {
                            Logger.Debug("An exeption occurred when trying to update macs with master list, set2. Ex: " + e); 
                        }


                        #endregion


                    #endregion
                }



                #endregion
            }
            else
            {
                #region Load Sensor data directly from Xml files

                    if (sensor_set_id.CompareTo("red") == 0)
                    {
                        #region Open the Xml File containing the sensor parameters for Set 1

                        try
                        {
                            if (File.Exists(Core.KERNEL_PATH + "\\updater_SensorData1.xml"))
                                wc.FromXML(Core.KERNEL_PATH + "\\updater_SensorData1.xml");
                            else
                                wc.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
                        }
                        catch
                        {
                            //TODO: Notify the user/researcher in this case
                            Logger.Debug("The SensorData1.Xml couldn't be opened.");
                        }

                        #endregion

                    }
                    else
                    {
                        #region Open the Xml File containing the sensor parameters for Set 2

                            try
                            {
                                if (File.Exists(Core.KERNEL_PATH + "\\updater_SensorData2.xml"))
                                    wc.FromXML(Core.KERNEL_PATH + "\\updater_SensorData2.xml");
                                else
                                    wc.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");
                            }
                            catch
                            {
                                //TODO: Notify the user/researcher in this case
                                Logger.Debug("The SensorData2.Xml couldn't be opened.");
                            }

                        #endregion
                    }

                #endregion 
            }

            //TODO:Check that MACs are valid, otherwise, notify user/researcher
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

               if (!Is_Kernel_Running())
                   Logger.Debug("Kernel is not running");
               else
                   Logger.Debug("Kernel is running");
                  //TODO: if kernel running kill it 

               bool is_kernel_started = false;


               if (!Core._KernalStarted)
               {
                   Logger.Debug("_KernelStarted variable is false ");

                   if (!Core.Start())
                   {
                       MessageBox.Show("failed to start kernel, restart app");
                       Logger.Debug("failed to start kernel: msg 1");
                       //KillKernel();
                       Core.Terminate();   
                   }
                   else
                   {
                       Thread.Sleep(5000);

                       Logger.Debug("Kernel started successfully: msg1");
                       is_kernel_started = true;

                       Thread.Sleep(5000);
                       Core.Ping();
                       Logger.Debug("Ping Kernel");
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
                           is_kernel_started = true;

                           Thread.Sleep(5000);
                           Core.Ping();
                           Logger.Debug("Ping Kernel");
                       }
                   }
                   else
                   {
                       MessageBox.Show("Failed to shutdown kernel");
                       Logger.Debug("Failed to shutdown the kernel");
                   }
               }


               if (!is_kernel_started)
               {
                   Logger.Debug("Failed to shutdown the kernel");
                   //Restart App
                   is_rebooting = false;
                   this.Close();
               }
 
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
                                UpdateMsg("Sensors Set");
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
                               
                               #region Hide the connect panel (commented)
                               //ConnectPanel.Enabled = false;
                               //ConnectPanel.Visible = false;
                               
                               ////Show the swap panel
                               //SwapPanel.BringToFront();
                               //SwapPanel.Enabled = true;
                               //SwapPanel.Visible = true;
                                #endregion

                               TurnOnPanel(PanelID.SWAP);

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

                              #region commented
                              ////Stop the connection status thread 
                                //if (ACsUpdateTimer.Enabled)
                                //    StopACsUpdater();
                                
                                //Thread.Sleep(1000);

                                ////Stop Kernel
                                //if (TerminateKernel())
                                //    UpdateMsg("Stopping Kernel");

                                ////Wait to stabilize system (2 secs)
                              //Thread.Sleep(1000);
                              #endregion 

                              #region Start The Swap Sequence (commented)

                              #region commented
                              //if disconnected, swap sensors if the app is running
                                //if (app_status.CompareTo("running") == 0){}
                                #endregion


                                //try
                                //{
                                //    //TODO: Register/Log the swap wockets event
                                //    UpdateMsg("Swap Wockets");
                                //    Logger.Debug("Starting to swap wockets, Current Set: " + sensor_set);

                                //    //Dispose the old wockets controller
                                //    wockets_controller.Dispose();
                                //    Thread.Sleep(1000);
                                //    Logger.Debug("Wockets controller disposed");

                                //    //Create new wockets controller
                                //    wockets_controller = new Wockets.WocketsController("", "", "");

                                //    //Determine which set will be used & load the corresponding Xml File
                                //    if (this.sensor_set.CompareTo("red") == 0)
                                //    {
                                //        sensor_set = "green";
                                //        wockets_controller.FromXML(Core.KERNEL_PATH + "\\updater_SensorData2.xml");
                                //    }
                                //    else
                                //    {
                                //        sensor_set = "red";
                                //        wockets_controller.FromXML(Core.KERNEL_PATH + "\\updater_SensorData1.xml");
                                //    }


                                //    //TODO: Check if macs against the master list file
                                //    //point kernel to new wockets controller
                                //    CurrentWockets._Controller = wockets_controller;

                                //    //Add the sensors macs to the sensor list
                                //    sensors_list.Clear();
                                //    for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                                //        sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);
                                    
                                //    //Update status message
                                //    UpdateMsg("Wockets Swapped");
                                //    Thread.Sleep(1000);
                                //    Logger.Debug("Finish loading new set from Xml, new set: " + sensor_set);


                                //    //--- Initialize Kernel  ---
                                //    ResetUploaderCounters();
                                //    ResetACsCounters(wockets_controller);
                                //    for (int i = 0; i < wockets_controller._Receivers.Count; i++)
                                //    {
                                //        PrevFullPkg[i] = 0;
                                //        PrevPartialPkg[i] = 0;
                                //        PrevEmptyPkg[i] = 0;
                                //    }
                                   

                                //    //== Restart kernel == (commented for now)
                                //    //SuscribeToKernelEvents();
                                //    //Start the kernel connection sequence
                                //    //StartLoadingWocketsToKernel();
                                //    //Update status message
                                //    //UpdateMsg("Kernel Started");
                                //    //Thread.Sleep(1000);

                                //    UpdateMsg("Verify Wockets");
                                //    Core.SetSensors(this.sensors_list);
                                //    Thread.Sleep(2000);
                                //    Logger.Debug("Set Sensors Command Sent");

                                //}
                                //catch
                                //{
                                //    Logger.Debug("Swap sequence after wockets disconnected failed.");
                                //}


                                #endregion

                              UpdateMsg("Stopping Kernel");

                                //Indicate the swap sequence in the status files
                                try
                                {
                                    //Save set ID to file
                                    StreamWriter wr_sensors = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_set.txt");
                                    
                                    //Determine which set will be used 
                                    if (this.sensor_set.CompareTo("red") == 0)
                                          sensor_set = "green";
                                    else
                                          sensor_set = "red";
                                    
                                    wr_sensors.WriteLine(sensor_set);
                                    wr_sensors.Flush();
                                    wr_sensors.Close();
                                }
                                catch
                                {
                                    Logger.Debug("An exception occurred after disconnected from kernel. When trying to save set id to file in the swapping process."); 
                                }


                                //close application & reboot
                                is_rebooting = true;
                                this.Close();
                                break;

                            default:
                                break;
                        }

                    }
                }
                catch
                {
                   Logger.Debug("exception in the kernel event listener");
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


      #region Audio Control Functions

          //Structures
           public enum SND_SOUNDTYPE
            {
                On,
                File,
                Vibrate,
                None
            }

           private enum SND_EVENT
            {
                All,
                RingLine1,
                RingLine2,
                KnownCallerLine1,
                RoamingLine1,
                RingVoip
            }

           [StructLayout(LayoutKind.Sequential)]
           private struct SNDFILEINFO
            {
                [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
                public string szPathName;
                [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
                public string szDisplayName;
                public SND_SOUNDTYPE sstType;
            }

           public enum Volumes : int
           {
               OFF = 0,

               LOW = 858993459,

               NORMAL = 1717986918,

               MEDIUM = -1717986919,

               HIGH = -858993460,

               VERY_HIGH = -1
           }


           //PInvokes
           [DllImport("coredll.dll")]
           public static extern void AudioUpdateFromRegistry();

           [DllImport("aygshell.dll", SetLastError = true)]
           private static extern uint SndSetSound(SND_EVENT seSoundEvent, ref SNDFILEINFO pSoundFileInfo, bool fSuppressUI);

           [DllImport("aygshell.dll", SetLastError = true)]
           private static extern uint SndGetSound(SND_EVENT seSoundEvent, ref SNDFILEINFO pSoundFileInfo);


           [DllImport("coredll.dll", SetLastError = true)]
           internal static extern int waveOutSetVolume(IntPtr device, int volume);

           [DllImport("coredll.dll", SetLastError = true)]
           internal static extern int waveOutGetVolume(IntPtr device, ref int volume);
           
           //Audio Functions
           private static void SetProfileNormal(SND_EVENT mysnd)
           {
               SNDFILEINFO soundFileInfo = new SNDFILEINFO();
               soundFileInfo.sstType = SND_SOUNDTYPE.On;
               uint num = SndSetSound(mysnd, ref soundFileInfo, true);
               AudioUpdateFromRegistry();

           }

           private static void SetProfileVibrate()
           {
               SNDFILEINFO soundFileInfo = new SNDFILEINFO();
               soundFileInfo.sstType = SND_SOUNDTYPE.Vibrate;
               uint num = SndSetSound(SND_EVENT.All, ref soundFileInfo, true);
               AudioUpdateFromRegistry();
           }

           private static void SetProfileMuted()
           {
               SNDFILEINFO soundFileInfo = new SNDFILEINFO();
               soundFileInfo.sstType = SND_SOUNDTYPE.None;
               uint num = SndSetSound(SND_EVENT.All, ref soundFileInfo, true);
               AudioUpdateFromRegistry();
           }

           private bool IsInVibrateMode()
           {
               SNDFILEINFO info = new SNDFILEINFO();
               SndGetSound(SND_EVENT.All, ref info);
               return (info.sstType == SND_SOUNDTYPE.Vibrate);
           }

           private bool IsMuted()
           {
               SNDFILEINFO info = new SNDFILEINFO();
               SndGetSound(SND_EVENT.All, ref info);
               return (info.sstType == SND_SOUNDTYPE.None);
           }

      
     #endregion



      #region Reboot Phone
        
        [DllImport("aygshell.dll")]
        private static extern bool ExitWindowsEx(uint uFlags, int dwReserved);
       
  
        enum ExitWindowsAction : uint
        {
            EWX_LOGOFF = 0,
            EWX_SHUTDOWN = 1,
            EWX_REBOOT = 2,
            EWX_FORCE = 4,
            EWX_POWEROFF = 8
        }


        void rebootDevice()
        {
           
            Logger.Debug("Rebooting");

            #region commented 1

            //try
            //{
            //    //Indicate that application was terminated in reboot mode
            //    StreamWriter wr_status = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_status.txt");
            //    wr_status.WriteLine("running");


            //    if (IsInVibrateMode())
            //        wr_status.WriteLine("vibrate");
            //    else
            //        wr_status.WriteLine("no_vibrate");

            //    if (IsMuted())
            //        wr_status.WriteLine("muted");
            //    else
            //        wr_status.WriteLine("no_muted");


            //    int volume = (int)0;
            //    waveOutGetVolume(IntPtr.Zero, ref volume);
            //    wr_status.WriteLine(volume.ToString());

            //    wr_status.Flush();
            //    wr_status.Close();
            //}
            //catch
            //{
            //    Logger.Debug("An exception occurred when saving the reboot status to file.");
            //}

            #endregion 


            #region commented 2

            //Mute Phone
            // waveOutSetVolume(IntPtr.Zero, (int)Volumes.OFF);

            //SetProfileMuted();
            //Thread.Sleep(1000);
            //Application.DoEvents();

            //if (this.app_status.CompareTo("normal_start") != 0)
            //{
            //DisplayPower.PowerOff();
            //SetDevicePower("BKL1:", PowerStateRequirement.POWER_NAME, CEDEVICE_POWER_STATE.D0);
            //SetSystemPowerState(null, PowerState.POWER_STATE_USERIDLE, 0);
            //}

            #endregion


            //Reboot
            ExitWindowsEx((uint)ExitWindowsAction.EWX_REBOOT, 0);
        }

        #region commented
        //private void button_reboot_phone_Click(object sender, EventArgs e)
        //{
        //    //try
        //    //{
        //    //    Logger.Debug("Starting to reboot the phone");

        //    //    //Stop status monitoring thread
        //    //    StopACsUpdater();

        //    //    //Wait for the system to stabilize and check that threads have finished
        //    //    Thread.Sleep(2000);

        //    //    //Terminate the kernel
        //    //    if (TerminateKernel()) 
        //    //    {
        //    //        this.messageWindow.Dispose();
        //    //        Application.Exit();
        //    //        rebootDevice();
        //    //    }
        //    //}
        //    //catch
        //    //{
        //    //    Logger.Debug("An exception occurred when trying to reboot the device");
        //    //}   


        //    //terminate uploader
        //    TerminateDataUploader();
        //    TerminateLogUploader();

        //}
        #endregion


      #endregion


      #region Reboot Phone


#region restart silently

       public enum SND_SOUNDTYPE
        {
            On,
            File,
            Vibrate,
            None
        }

       private enum SND_EVENT
        {
            All,
            RingLine1,
            RingLine2,
            KnownCallerLine1,
            RoamingLine1,
            RingVoip
        }

       [StructLayout(LayoutKind.Sequential)]
       private struct SNDFILEINFO
        {
            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
            public string szPathName;
            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
            public string szDisplayName;
            public SND_SOUNDTYPE sstType;
        }

       [DllImport("coredll.dll")]
       public static extern void AudioUpdateFromRegistry();

       [DllImport("aygshell.dll", SetLastError = true)]
       private static extern uint SndSetSound(SND_EVENT seSoundEvent, ref SNDFILEINFO pSoundFileInfo, bool fSuppressUI);

       [DllImport("aygshell.dll", SetLastError = true)]
       private static extern uint SndGetSound(SND_EVENT seSoundEvent, ref SNDFILEINFO pSoundFileInfo);


       static void SetProfileNormal(SND_EVENT mysnd)
       {
           SNDFILEINFO soundFileInfo = new SNDFILEINFO();
           soundFileInfo.sstType = SND_SOUNDTYPE.On;
           uint num = SndSetSound(mysnd, ref soundFileInfo, true);
           AudioUpdateFromRegistry();

       }

       static void SetProfileVibrate()
       {
           SNDFILEINFO soundFileInfo = new SNDFILEINFO();
           soundFileInfo.sstType = SND_SOUNDTYPE.Vibrate;
           uint num = SndSetSound(SND_EVENT.All, ref soundFileInfo, true);
           AudioUpdateFromRegistry();
       }

       static void SetProfileMuted()
       {
           SNDFILEINFO soundFileInfo = new SNDFILEINFO();
           soundFileInfo.sstType = SND_SOUNDTYPE.None;
           uint num = SndSetSound(SND_EVENT.All, ref soundFileInfo, true);
           AudioUpdateFromRegistry();
       }

       private bool IsInVibrateMode()
       {
           SNDFILEINFO info = new SNDFILEINFO();
           SndGetSound(SND_EVENT.All, ref info);
           return (info.sstType == SND_SOUNDTYPE.Vibrate);
       }

       private bool IsMuted()
       {
           SNDFILEINFO info = new SNDFILEINFO();
           SndGetSound(SND_EVENT.All, ref info);
           return (info.sstType == SND_SOUNDTYPE.None);
       }


       public enum Volumes : int
       {
           OFF = 0,

           LOW = 858993459,

           NORMAL = 1717986918,

           MEDIUM = -1717986919,

           HIGH = -858993460,

           VERY_HIGH = -1
       }


       [DllImport("coredll.dll", SetLastError = true)]
        internal static extern int waveOutSetVolume(IntPtr device, int volume);

       [DllImport("coredll.dll", SetLastError = true)]
        internal static extern int waveOutGetVolume(IntPtr device, ref int volume);
       


#endregion


        [DllImport("aygshell.dll")]
        private static extern bool ExitWindowsEx(uint uFlags, int dwReserved);
         
        enum ExitWindowsAction : uint
        {
            EWX_LOGOFF = 0,
            EWX_SHUTDOWN = 1,
            EWX_REBOOT = 2,
            EWX_FORCE = 4,
            EWX_POWEROFF = 8
        }


        void rebootDevice()
        {
           
            Logger.Debug("save the device status to file, before rebooting");

            try
            {
               
                //Indicate that application was terminated in reboot mode
                StreamWriter wr_status = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_status.txt");
                wr_status.WriteLine("running");


                if (IsInVibrateMode())
                    wr_status.WriteLine("vibrate");
                else
                    wr_status.WriteLine("no_vibrate");

                if (IsMuted())
                    wr_status.WriteLine("muted");
                else
                    wr_status.WriteLine("no_muted");


                int volume = (int)0;
                waveOutGetVolume(IntPtr.Zero, ref volume);
                wr_status.WriteLine(volume.ToString());

                wr_status.Flush();
                wr_status.Close();
            }
            catch
            {
                Logger.Debug("An exception occurred when saving the reboot status to file.");
            }

            //Mute Phone
           // waveOutSetVolume(IntPtr.Zero, (int)Volumes.OFF);

            //SetProfileMuted();
            Thread.Sleep(1000);
            //Application.DoEvents();

            //if (this.app_status.CompareTo("normal_start") != 0)
            //{
                //DisplayPower.PowerOff();
            SetDevicePower("BKL1:", PowerStateRequirement.POWER_NAME, CEDEVICE_POWER_STATE.D0);
            SetSystemPowerState(null, PowerState.POWER_STATE_USERIDLE, 0);
            //}
            
            //Reboot
            ExitWindowsEx((uint)ExitWindowsAction.EWX_REBOOT, 0);
        }


        private void button_reboot_phone_Click(object sender, EventArgs e)
        {
            try
            {
                Logger.Debug("Starting to reboot the phone");

                //Stop status monitoring thread
                StopACsUpdater();

                //Wait for the system to stabilize and check that threads have finished
                Thread.Sleep(2000);

                //Terminate the kernel
                if (TerminateKernel()) 
                {
                    this.messageWindow.Dispose();
                    Application.Exit();
                    rebootDevice();
                }
            }
            catch
            {
                Logger.Debug("An exception occurred when trying to reboot the device");
            }   
        }

      
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

                #region Check which panel is open (commented)

                    //string panel_open = "";

                    ////Hide the swap panel
                    //if (SwapPanel.Visible)
                    //{
                    //    SwapPanel.Visible = false;
                    //    SwapPanel.Enabled = false;
                    //    panel_open = "Swap";
                    //}
                    ////Hide the main actions panel
                    //if (MainActionsPanel.Visible)
                    //{
                    //    MainActionsPanel.Visible = false;
                    //    MainActionsPanel.Enabled = false;
                    //    panel_open = "Main";
                    //}
                    ////Hide the upload panel
                    //if (UploadDataPanel.Visible)
                    //{
                    //    UploadDataPanel.Visible = false;
                    //    UploadDataPanel.Enabled = false;
                    //    panel_open = "Upload";
                    //}
                    ////Hide the sensors status panel
                    //if (SensorStatusPanel.Visible)
                    //{
                    //    SensorStatusPanel.Visible = false;
                    //    SensorStatusPanel.Enabled = false;
                    //    panel_open = "Status";
                    //}

                #endregion


                //Show the connect status panel
                label_kernel_status.Text = "...";

                TurnOnPanel(PanelID.CONNECTION);

                #region commented
                //ConnectPanel.BringToFront();
                //ConnectPanel.Visible = true;
                //ConnectPanel.Enabled = true;
                #endregion


                Application.DoEvents();


                if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                {

                    #region user confirmed to exit app

                    label_kernel_status.Text = "Exiting Application";
                    Application.DoEvents();

                    Logger.Debug("user confirmed to quit the application");

                    try
                    {
                        //Indicate that application was terminated by the user
                        StreamWriter wr_status = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_status.txt");
                        //wr_status.WriteLine("normal_start");
                        wr_status.WriteLine("running");

                        #region commented
                        //if (IsInVibrateMode())
                        //    wr_status.WriteLine("vibrate");
                        //else
                        //    wr_status.WriteLine("no_vibrate");

                        //if (IsMuted())
                        //    wr_status.WriteLine("muted");
                        //else
                        //    wr_status.WriteLine("no_muted");
                        #endregion 


                        if (IsInVibrateMode())
                            wr_status.WriteLine("vibrate");
                        else
                            wr_status.WriteLine("no_vibrate");

                        if (IsMuted())
                            wr_status.WriteLine("muted");
                        else
                            wr_status.WriteLine("no_muted");

                        wr_status.Flush();
                        wr_status.Close();
                    }
                    catch
                    {
                        Logger.Debug("An exception occurred when saving app status to file.");
                    }

                    TerminateApp();


                    #endregion

                }
                else
                {
                        //Hide the connect panel
                        //ConnectPanel.Visible = false;
                        //ConnectPanel.Enabled = false;
                    #region Show the panel that was originally open (commented)

                    //switch (panel_open)
                    //{
                    //    case "Swap":
                    //        SwapPanel.BringToFront();
                    //        SwapPanel.Visible = true;
                    //        SwapPanel.Enabled = true;
                    //        break;
                    //    case "Main":
                    //        MainActionsPanel.BringToFront();
                    //        MainActionsPanel.Visible = true;
                    //        MainActionsPanel.Enabled = true;
                    //        break;
                    //    case "Upload":
                    //        UploadDataPanel.BringToFront();
                    //        UploadDataPanel.Visible = true;
                    //        UploadDataPanel.Enabled = true;
                    //        break;
                    //    case "Status":
                    //        SensorStatusPanel.BringToFront();
                    //        SensorStatusPanel.Visible = true;
                    //        SensorStatusPanel.Enabled = true;
                    //        break;

                    //    default:
                    //        break;
                    //}

                    #endregion


                    TurnOnPanel(LastPanel);
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

                #region commented
                ////Hide the swap panel
                //SwapPanel.Enabled = false;
                //SwapPanel.Visible = false;

                //Show the connect panel
               
                //ConnectPanel.BringToFront();
                //ConnectPanel.Enabled = true;
                //ConnectPanel.Visible = true;
                #endregion


                label_kernel_status.Text = "Load Wockets";
                TurnOnPanel(PanelID.CONNECTION);

                //Start the kernel connection sequence
                StartLoadingWocketsToKernel();
                
                Logger.Debug("Start loading wockets to kernel thread started");

                #endregion

                menuQuitApp.Text = "Quit";
                menuQuitApp.Enabled = true;

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
            catch(Exception e)
            {
                Logger.Debug("An exception occurred when trying to terminate kernel. ex:" + e);
                //TODO: Here try more agressive methods to stop the kernel
                return false;
            }
        }



        private bool Is_Kernel_Running()
        {
            try
            {
                bool found = false;
                ProcessInfo[] processes = ProcessCE.GetProcesses();
                if (processes != null)
                {
                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("Kernel.exe") >= 0)
                        {
                            found = true;
                            break;
                        }
                    }   
                }

                return found;
            }
            catch
            {   
                return false;
            }
        }


        private bool Is_Kernel_Running(out System.Diagnostics.Process kprocess)
        {
            kprocess = null;

            try
            {
                ProcessInfo[] processes = ProcessCE.GetProcesses();

                if (processes != null)
                {
                    bool found = false;

                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("Kernel.exe") >= 0)
                        {
                            
                            kprocess = System.Diagnostics.Process.GetProcessById((int)processes[i].Pid);
                            Logger.Debug("The kernel process was found.");
                            found = true;
                            break;
                        }
                    }

                    return found;
                }
                else
                {
                    Logger.Debug("The kernel process was NOT found.");
                    return false; 
                }

            }
            catch (Exception ex)
            {
                Logger.Debug("An exception occureed when trying to find the kernel." + ex);
                return false;
            }
        }

    
        private void KillKernel()
        {
            //Terminate kernel if running
            try
            {
                System.Diagnostics.Process kernel_process = null;

                if (Is_Kernel_Running(out kernel_process))
                {
                    if (kernel_process != null)
                    {
                        kernel_process.Close();
                        //uploader_process.Dispose();
                        kernel_process.Kill();
                    }
                }
            }
            catch(Exception e)
            {
                Logger.Debug("An exception occurred when trying to kill the kernel process.");
            }
        }


        private void TerminateLogUploader()
        {
            //Termine uploader if running
            try
            {
                System.Diagnostics.Process uploader_process = null;
                if (Is_LogUploader_Running(out uploader_process))
                {
                    if (uploader_process != null)
                    {
                        //uploader_process.Close();
                        //uploader_process.Dispose();
                        uploader_process.Kill();
                        Thread.Sleep(500);
                        
                    }
                }
            }
            catch(Exception  e)
            {
                Logger.Debug("An exception occurred when trying to terminate the log uploader.");
            }
        }


        private void TerminateDataUploader()
        {
            //Termine uploader if running
            try
            {
                System.Diagnostics.Process uploader_process = null;
                if (Is_DataUploader_Running(out uploader_process))
                {
                    if (uploader_process != null)
                    {
                        //uploader_process.Close();
                        //uploader_process.Dispose();
                        uploader_process.Kill();
                        Thread.Sleep(500);
                    }
                }
            }
            catch
            {
                Logger.Debug("An exception occurred when trying to terminate the data uploader.");
            }
        }


        public void TerminateApp()
        {
            try
            {
                Logger.Debug("Starting to quit application");

                //Stop status monitoring thread
                StopACsUpdater();
               
                //Wait for the system to stabilize and check that threads have finished
                Thread.Sleep(1000);

                //Termine uploaders if running
                TerminateDataUploader();
                TerminateLogUploader();

                //Wait to stabilize system (2 secs)
                //Thread.Sleep(1000);

                //Terminate the kernel

                if ( !TerminateKernel()) //=== if (!Core._KernalStarted)
                   Logger.Debug("Failed to terminate kernel, exection when forcing to quit");

                //Terminate hidden window 
                this.messageWindow.Dispose();

                //Terminate app
                Application.Exit();
             
            }
            catch
            {
                Logger.Debug("An exception occurred when trying to quit the application");
            }
        }


       
       
        private void WocketsMainForm_Closing(object sender, CancelEventArgs e)
        {
            TerminateApp();

            #region commented
            
        //    if (!is_rebooting)
        //      TerminateApp();
        //    else
        //    {
        //        try
        //        {
        //            //Termine uploader if running
        //            TerminateUploader();

        //            //Wait to stabilize system (2 secs)
        //            Thread.Sleep(1000);

        //            this.messageWindow.Dispose();
        //            Application.Exit();
        //        }
        //        catch
        //        {   Logger.Debug("An exception occurred when trying to quit the application for rebooting.");
        //        }
            //    }
            #endregion

        }
        

        private void WocketsMainForm_Closed(object sender, EventArgs e)
        {

            try
            {
                if (!is_rebooting)
                {
                    Logger.Debug("The application quit successfully.");
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
                else
                {
                    Logger.Debug("The phone is rebooting.");
                    rebootDevice();
                }
            }
            catch
            {
                Logger.Debug("An exception occurred when executing the kill process command.");
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
                   

                    #region Check which panel is open (commented)

                    ////Hide the swap panel
                    //if (SwapPanel.Visible)
                    //{
                    //    SwapPanel.Visible = false;
                    //    SwapPanel.Enabled = false;
                    //}
                    //else if (UploadDataPanel.Visible)
                    //{
                    //    UploadDataPanel.Visible = false;
                    //    UploadDataPanel.Enabled = false;
                    //    StopUpdateUploadThread();

                    //   //Hide the elapsed time label
                    //   textBox_elapsed_time.Visible = false;
                    //}
                    //else if (SensorStatusPanel.Visible)
                    //{
                    //    SensorStatusPanel.Visible = false;
                    //    SensorStatusPanel.Enabled = false;
                    //}

                    

                    //Show Main Actions Panel
                    //MainActionsPanel.Visible = true;
                    //MainActionsPanel.BringToFront();
                    //MainActionsPanel.Enabled = true;

                    #endregion

                    TurnOnPanel(PanelID.MAIN);
                    Logger.Debug("Go to the main menu panel");
                    
                }
            }
            catch(Exception ex) 
            {
                Logger.Debug("An exception occurred when minimizing/main menu button clicked. ex: " + ex);      
            }
        }

        private void Minimize_Main_Window()
        {
            ShowWindow(this.Handle, SW_MINIMIZED);
        }

    #endregion 

      
    
      #region Main Actions Panel Buttons

        //Swap Button Panel
        private void SelectSensorsButton_Click(object sender, EventArgs e)
        {
            SelectSensorsButton.Enabled = false;
            Logger.Debug("Go to the Swap Panel");

            #region commented
            ////Hide Connect Panel
            //ConnectPanel.Visible = false;
            //ConnectPanel.Enabled = false;

            ////Hide Sensors Status Panel
            //SensorStatusPanel.Visible = false;
            //SensorStatusPanel.Enabled = false;

            ////Hide Upload Panel
            //UploadDataPanel.Visible = false;
            //UploadDataPanel.Enabled = false;

            ////Hide Main Actions Panel
            //MainActionsPanel.Visible = false;
            //MainActionsPanel.Enabled = false;

            ////Show Swap Panel
            //SwapPanel.BringToFront();
            //SwapPanel.Visible = true;
            //SwapPanel.Enabled = true;
            #endregion

            ////Update Main App Actions Menu
            menuMainAppActions.Text = "Main Menu";
            TurnOnPanel(PanelID.SWAP);
            SelectSensorsButton.Enabled = true;
        }

        //Upload Button
        private void UploadDataActionButton_Click(object sender, EventArgs e)
        {
            UploadDataActionButton.Enabled = false;
            Logger.Debug("Go to the upload panel");

            #region commented
            ////Hide Connect Panel
            //ConnectPanel.Visible = false;
            //ConnectPanel.Enabled = false;

            ////Hide Sensors Status Panel
            //SensorStatusPanel.Visible = false;
            //SensorStatusPanel.Enabled = false;

            ////Hide Main Actions Panel
            //MainActionsPanel.Visible = false;
            //MainActionsPanel.Enabled = false;

            ////Hide Swap Panel
            //SwapPanel.Visible = false;
            //SwapPanel.Enabled = false;

            ////Show Upload Panel
            //UploadDataPanel.BringToFront();
            //UploadDataPanel.Visible = true;
            //UploadDataPanel.Enabled = true;
            #endregion

            //Update Main App Actions Menu
            menuMainAppActions.Text = "Main Menu";
            TurnOnPanel(PanelID.UPLOAD);

            //Show elapsed time timer label
            textBox_elapsed_time.Visible = true;

            //Launch the update upload and timer thread
            StartUpdateUploadThread();
            UploadDataActionButton.Enabled = true;

        }


        //Detail Status Button
        private void SensorsStatusButton_Click(object sender, EventArgs e)
        {
            SensorsStatusButton.Enabled = false;
            Logger.Debug("Go to the sensor status panel");

            #region commented
            ////Hide Connect Panel
            //ConnectPanel.Visible = false;
            //ConnectPanel.Enabled = false;

            ////Hide Upload Panel
            //UploadDataPanel.Visible = false;
            //UploadDataPanel.Enabled = false;

            ////Hide Main Actions Panel
            //MainActionsPanel.Visible = false;
            //MainActionsPanel.Enabled = false;

            ////Hide Swap Panel
            //SwapPanel.Visible = false;
            //SwapPanel.Enabled = false;

            ////Show Sensor Status Panel
            //SensorStatusPanel.BringToFront();
            //SensorStatusPanel.Visible = true;
            //SensorStatusPanel.Enabled = true;
            #endregion 

            #region commented
            //Load ACs To Kernel
            //Core.READ_EMPTY_RECEIVED_COUNT();
            //Core.READ_FULL_RECEIVED_COUNT();
            //Core.READ_PARTIAL_RECEIVED_COUNT();
            //TODO: Launch the thread to read sensors ACs
            //StartACsUpdater();
            #endregion


            //Update Main App Actions Menu
            menuMainAppActions.Text = "Main Menu";
            TurnOnPanel(PanelID.STATUS);

            SensorsStatusButton.Enabled = true;

        }

    #endregion

      
      #region Data Uploader
        
        //Upload Button From UploadDataPanel
        private void UploadButton_Click(object sender, EventArgs e)
        {
            UploadButton.Enabled = false;
            Logger.Debug("upload data button clicked");

            if (!Is_DataUploader_Running())
            {
                if (!Is_LogUploader_Running())
                    LaunchDataUploader();
                else
                {
                    //Terminate Log Uploader
                    label_upload_data_status.Text = "Uploading Data Logs, Please Wait...";
                    label_upload_data_status.ForeColor = Color.Orange;
                    Application.DoEvents();
                    TerminateLogUploader();

                    //Start Data Uploader
                    label_upload_data_status.Text = "Starting Data Uploader...";
                    label_upload_data_status.ForeColor = Color.Orange;
                    Application.DoEvents();

                    LaunchDataUploader();
                }
            }
        }

        private void LaunchDataUploader()
        {
            
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
                    label_upload_data_status.Text = "Uploading Raw Data";
                    label_upload_data_status.ForeColor = Color.Green;
                    UploadButton.Enabled = false;
                }
                else
                {
                    label_upload_data_status.Text = "The data upload couldn't start.";
                    label_upload_data_status.ForeColor = Color.DimGray;
                    UploadButton.Enabled = true;
                }

                //TODO: Add an asynchronous sleep here
            }
            catch (Exception ex)
            {
                UploadButton.Enabled = true;
                Logger.Debug("An exception occureed when trying to launch the data uploader.exe program. ex: " + ex);
            }
        
        }

        private bool Is_DataUploader_Running()
        {
            bool found = false;

            try
            {
                ProcessInfo[] processes = ProcessCE.GetProcesses();

                if (processes != null)
                {
                   
                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("DataUploader.exe") >= 0)
                        {
                            found = true;
                            break;
                        }
                    }


                    #region commented
                    ////update status
                    //if (found)
                    //{
                    //    label_upload_data_status.Text = "Uploading Raw Data";
                    //    label_upload_data_status.ForeColor = Color.Green;
                    //    this.UploadButton.Enabled = false;

                    //    Logger.Debug("The data uploader is running.");
                    //    return true;
                    //}
                    //else
                    //{
                    //    label_upload_data_status.Text = "...";
                    //    label_upload_data_status.ForeColor = Color.DimGray;
                    //    this.UploadButton.Enabled = true;
                    //    Logger.Debug("The data uploader is NOT running.");
                    //    return false;
                    //}
                    #endregion 


                    return found;
                }
                else
                { return false; }
            }
            catch (Exception e)
            {
                Logger.Debug("An exception occureed when inquiring if the uploader is running.");
                return false;
            }
        }

        private bool Is_DataUploader_Running(out System.Diagnostics.Process uprocess)
        {
            uprocess = null;
            bool found = false;

            try
            {
                ProcessInfo[] processes = ProcessCE.GetProcesses();

                if (processes != null)
                {
                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("DataUploader.exe") >= 0)
                        {
                            uprocess = System.Diagnostics.Process.GetProcessById((int)processes[i].Pid);
                            found = true;
                            break;
                        }
                    }

                    //update status
                    if (found)
                       Logger.Debug("The data uploader is running.");
                    else
                       Logger.Debug("The data uploader is NOT running.");

                    return found;
                }
                else
                { return false; }
            }
            catch (Exception ex)
            {
                Logger.Debug("An exception occureed when inquiring if the data uploader is running, with get process." + ex);
                return false;
            }
        }


     #endregion

     
      #region Log Uploader

        private bool LaunchLogUploader()
        {
            try
            {
                //uploadCounter = 0;
                //prevFailed = prevSuccessful = -1;

                //Launch the uploader process
                ProcessStartInfo startInfo = new ProcessStartInfo();
                startInfo.WorkingDirectory = Core.KERNEL_PATH;               //+ "wocketsuploader\\";
                startInfo.FileName = Core.KERNEL_PATH + "LogUploader.exe";   //"wocketsuploader\\" + "LogUploader.exe";
                startInfo.UseShellExecute = false;
                _LogUploaderProcess = System.Diagnostics.Process.Start(startInfo.FileName, "");

                //update status
                if ( _LogUploaderProcess != null)
                {
                    label_upload_data_status.Text = "Uploading Data Logs";
                    label_upload_data_status.ForeColor = Color.Green;
                    Logger.Debug("the logUploader.exe program was launched.");
                    return true;
                }
                else
                {
                    label_upload_data_status.Text = "The log upload couldn't start";
                    label_upload_data_status.ForeColor = Color.DimGray;
                    Logger.Debug("the logUploader.exe program could't start.");
                    return false;
                }

                //TODO: Add an asynchronous sleep here
            }
            catch (Exception ex)
            {
                Logger.Debug("An exception occureed when trying to launch the logUploader.exe program");
                return false;
            }
        }

        private bool Is_LogUploader_Running()
        {
            try
            {
                ProcessInfo[] processes = ProcessCE.GetProcesses();

                if (processes != null)
                {
                    bool found = false;
                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("LogUploader.exe") >= 0)
                        {
                            found = true;
                            break;
                        }
                    }

                    //update status
                    if (found)
                    {
                        //label_upload_data_status.Text = "Uploading Data Logs";
                        //label_upload_data_status.ForeColor = Color.Green;
                        Logger.Debug("The log uploader is running.");
                        return true;
                    }
                    else
                    {
                        //label_upload_data_status.Text = "...";
                        //label_upload_data_status.ForeColor = Color.DimGray;
                        Logger.Debug("The log uploader is NOT running.");
                        return false;
                    }
                }
                else
                { return false; }
            }
            catch (Exception e)
            {
                Logger.Debug("An exception occureed when inquiring if the log uploader is running.");
                return false;
            }
        }

        private bool Is_LogUploader_Running(out System.Diagnostics.Process uprocess)
        {
            uprocess = null;

            try
            {
                ProcessInfo[] processes = ProcessCE.GetProcesses();

                if (processes != null)
                {
                    bool found = false;
                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("LogUploader.exe") >= 0)
                        {
                            uprocess = System.Diagnostics.Process.GetProcessById((int)processes[i].Pid);
                            found = true;
                            break;
                        }
                    }

                    //update status
                    if (found)
                    {  Logger.Debug("The log uploader is running.");
                        return true;
                    }
                    else
                    {Logger.Debug("The log uploader is NOT running.");
                        return false;
                    }

                }
                else
                { return false; }
            }
            catch (Exception ex)
            {

                Logger.Debug("An exception occureed when inquiring if the log uploader is running, with get process." + ex);
                return false;

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


    #region File Upload Update Callback

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

                  if (counter == 6) //enter every 3 secs
                  {

                      #region Update the Raw Data Uploaded Status 

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


                      #region commented
                      //If finished uploading, reset counter
                      //if ((prevSuccessful != CurrentWockets._UploadSuccessFiles) ||
                      //    (prevFailed != CurrentWockets._UploadFailedFiles))
                      //    uploadCounter = 0;
                      #endregion 


                      //update counters
                      prevSuccessful = CurrentWockets._UploadSuccessFiles;
                      prevFailed = CurrentWockets._UploadFailedFiles;

                      #endregion


                      
                      #region Determine if the uploader program is still running


                      #region commented

                      //try
                      //{
                      //    ProcessInfo[] processes = ProcessCE.GetProcesses();

                      //    if (processes != null)
                      //    {
                      //        bool found = false;
                      //        for (int i = 0; (i < processes.Length); i++)
                      //        {
                      //            if (processes[i].FullPath.IndexOf("DataUploader.exe") >= 0)
                      //            {
                      //                found = true;
                      //                break;
                      //            }
                      //        }

                      //        //update status
                      //        if (found)
                      //        {
                      //            label_upload_data_status.Text = "Uploading Raw Data";
                      //            label_upload_data_status.ForeColor = Color.Green;
                      //            this.UploadButton.Enabled = false;
                      //        }
                      //        else
                      //        {
                      //            label_upload_data_status.Text = "...";
                      //            label_upload_data_status.ForeColor = Color.DimGray;
                      //            this.UploadButton.Enabled = true;
                      //        }    

                      //    }
                      //}
                      //catch (Exception e){ }

                      #endregion 

                      if ( Is_DataUploader_Running())
                      {
                          label_upload_data_status.Text = "Uploading Raw Data";
                          label_upload_data_status.ForeColor = Color.Green;
                          this.UploadButton.Enabled = false;
                      }
                      else
                      {
                          if (Is_LogUploader_Running())
                          {
                              label_upload_data_status.Text = "Uploading Data Logs";
                              label_upload_data_status.ForeColor = Color.Green;
                              this.UploadButton.Enabled = true;
                          }
                          else
                          {
                              label_upload_data_status.Text = "...";
                              label_upload_data_status.ForeColor = Color.DimGray;
                              this.UploadButton.Enabled = true;
                          }
                      
                      }

                      #endregion


                      #region commented
                      //if (_UploaderProcess == null )
                      //{
                      //    label_upload_data_status.Text = "...";
                      //    label_upload_data_status.ForeColor = Color.DimGray;
                      //    this.UploadButton.Enabled = true;
                      //}
                      //else if ((!this.UploadButton.Enabled) && ((_UploaderProcess != null) && (_UploaderProcess.HasExited)))
                      //{
                      //    label_upload_data_status.Text = "...";
                      //    label_upload_data_status.ForeColor = Color.DimGray;
                      //    this.UploadButton.Enabled = true;
                      //}
                      #endregion



                      counter = 0;

                  }

                  this.Invalidate();
              }
          }
      }

    #endregion



    #region Read ACs for Sensor Status


     private void ResetUploaderCounters()
      {
          try
          {
              Core.WRITE_LAST_UPLOAD_FAILEDFILES(0);
              Core.WRITE_LAST_UPLOAD_SUCCESSFILES(0);
              Core.WRITE_LAST_UPLOAD_NEWFILES(0);
          }
          catch
          {
              Logger.Debug("An exception occurred when trying to reset Uploader counters");
          }
      }

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



     double WAIT_INTERVAL_LOG_UPLOADER = 60.0; //in minutes
     double WAIT_INTERVAL_DATA_UPLOADER_HRS = 1.0; //in hours


     private void ACsUpdateTimer_Tick(object sender, EventArgs e)
     {
         bool received_count_read = false;

         #region Update Sensors Connection Status
         
         
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

        #endregion

         #region Determine if the log/data uploader needs to be launched

         try 
         {  

            //Launch the data uploader at midnight once a day
            DateTime current_time = DateTime.Now;

            //Launch log uploader every hour
            ElapsedTime_LogUpload = current_time.Subtract(LastLogUploadInvoke);

            if (ElapsedTime_LogUpload.TotalMinutes > WAIT_INTERVAL_LOG_UPLOADER)
            {

                if (!Is_DataUploader_Running())
                {
                    bool launch_log_uploader = true;

                    if (current_time.Hour >= 1 && current_time.Hour <= 5)
                    {
                        Core.READ_LAST_UPLOAD_TIME();
                        ElapsedTime_DataUpload = current_time.Subtract(CurrentWockets._UploadLastTime);

                        if (ElapsedTime_DataUpload.TotalHours > WAIT_INTERVAL_DATA_UPLOADER_HRS)
                        {
                            if (Is_LogUploader_Running())
                            {
                                TerminateLogUploader();
                                Thread.Sleep(1000);
                            }

                            LaunchDataUploader();
                            launch_log_uploader = false;
                        }
                    }


                    if (launch_log_uploader)
                    {
                        // if uploader is NOT running, launch it 
                        if (!Is_LogUploader_Running())
                            LaunchLogUploader();
                    }
                }

                LastLogUploadInvoke = current_time;
            }
         }
         catch 
         {   
             Logger.Debug("An exeption occurred when invoking the log uploader.");
         }

        #endregion

     }


     private void StartACsUpdater()
        {
            ACsUpdateTimer.Enabled = true;
        }

     private void StopACsUpdater()
        {
            ACsUpdateTimer.Enabled = false;
        }

       


     #region Update ACs Event Listener (commented)

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