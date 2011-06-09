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
using Wockets.Utils;
using Wockets.Utils.IPC;
using Wockets.Data.Configuration;
using Wockets.Data.Types;
using Wockets.Decoders.Accelerometers;
using Wockets.Receivers;




namespace CollectDataUser
{

    enum PanelID 
    {
        SETTINGS,
        SETTINGS_OPTIONS,
        SETTINGS_DETAILS,
        SWAP,
        UPLOAD,
        STATUS,
        PACKETS,
        CONNECTION,
        LOCATION,
        BLANK,
        PREPARE_SET,
        LOCATION_BUTTONS,
        VERIFY_W_SENSOR,
        VERIFY_A_SENSOR,
        SWAP_COMPLETED,
        NONE
    }

    enum MasterListParam
    {
        Subject_ID,     //Participant ID
        IMEI,               //phone ID
        Set1_ID,            //set color
        Set1_ForceUpdate,   //yes, no
        Set1_MAC_Acc0,      //mac sensor 0
        Set1_MAC_Acc1,      //mac sensor 1
        Set1_MAC_Acc2,      //mac sensor 1
        Set2_ID,
        Set2_ForceUpdate,
        Set2_MAC_Acc0,
        Set2_MAC_Acc1,
        Set2_MAC_Acc2,
        UploadRawData,          //Specifies if raw data needs to be uploaded
        Length
    }

    

    public partial class WocketsMainForm : Form
    {


        #region Variables

        //General Status Variables
        private String sensor_set = "";
        private String app_status = "running";
        private String software_version = "";
        private bool is_rebooting = false;
        private bool upload_raw_data = true;
        private string firstCard = "";
        private string subjectID = "0";

        //General Application Logger
        private LocalLogger appLogger = null;

        
        //Data Uploader
        private Thread uploadThread;
        private static System.Diagnostics.Process _UploaderProcess = null;
        private static System.Diagnostics.Process _LogUploaderProcess = null;

      
        //uploaded files counters
        private bool disposed = false;
        private int counter = 0;
        
        // Events Variables
        private CustomSynchronizedLogger UploadLoggerEvents = null;
        private int swap_event     = 0;
        private int restart_event  = 0;
        private int locationChanged_event = 0;


        //--- Connection Status Monitoring ---
        System.Windows.Forms.Timer ACsUpdateTimer;

        private int MAX_NUMBER_OF_SENSORS = 2;
        private int[] PrevFullPkg = null;
        private int[] PrevPartialPkg = null;
        private int[] PrevEmptyPkg = null;
        private DateTime[] LastPkgTime = null;
        private TimeSpan[] ElapsedConnectionTime = null;

        private DateTime LastLogUploadInvoke;
        private TimeSpan ElapsedTime_LogUpload;

        private TimeSpan ElapsedTime_DataUpload;
       
        //System Wide Lock
        public static string APP_LOCK = "APPLock";
        private static Semaphore appLock = new Semaphore(1, 1, APP_LOCK);

        //Internal Message Window
        private internalMessageWindow messageWindow;
        public IntPtr wndPtr;


        //Wockets Controller
        private static WocketsController wockets_controller = null;
        public  static bool _WocketsRunning = false;
        private string[] sensor_data = null;
        private bool sensors_loaded = false;
        //private string WOCKETS_ROOT_PATH = @"\Program Files\wockets\";
        //private static string rootStorageDirectory = "";
        

        #region -- PInvokes --
        //Find the Internal Message Window
        [DllImport("coredll.dll")]
        public static extern IntPtr FindWindow(string lpClassName, string lpWindowName);

        //Minimize the Window Form
        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
        const int SW_MINIMIZED = 6;
        const int SW_NORMAL = 1;

        #endregion 


         
        #endregion 


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


            #region Read the Software Version
                
            #region commented
            //System.Reflection.Assembly a = System.Reflection.Assembly.GetExecutingAssembly();
            //System.Reflection.AssemblyName an = a.GetName();
            //software_version = "Version: " + an.Version.ToString();
            //this.label_software_version.Text = software_version.Substring(0, 14);
            #endregion

            software_version = "Version: " + "1.53";
            this.label_software_version.Text = software_version;

            #endregion
          

            #region Read Phone IMEI

            label_phone_IMEI.Text = CurrentPhone._IMEI;

            #endregion

            
            #region Identify the Storage Card

            Settings._MemoryCardDirectory =  "\\Storage Card";

            firstCard = GetStorageCardName(5);

            if (firstCard.Length == 0)
            {
                Settings._MemoryCardDirectory = "\\Mock Storage Card";

                if ( !Directory.Exists(Settings._MemoryCardDirectory) )
                    Directory.CreateDirectory(Settings._MemoryCardDirectory);
            }
            
            
            #endregion


            #region Initialize Root Directories
            
            try
            {
                Settings._MainWocketsDirectory = "\\Program Files\\wockets\\";
                
                //Indicate the images directory
                NEEDED_FILES_PATH = Settings._MainWocketsDirectory + "NeededFiles\\";
                LOCATION_IMAGES_DIRECTORY = NEEDED_FILES_PATH + "images\\siluette\\";

                //Create the root storage directory
                Settings._RootStorageDirectory = Settings._MemoryCardDirectory + "\\Wockets\\";

                if (!Directory.Exists(Settings._RootStorageDirectory))
                    Directory.CreateDirectory(Settings._RootStorageDirectory);

                //Initialize the session and log directories
                UpdateDataStorageDirectoryPath();

                //Initialize the upload logger
                bool success_event_logger = false;
                UploadLoggerEvents = new CustomSynchronizedLogger("events", Settings._MemoryCardDirectory, out success_event_logger);
                
                if( success_event_logger )
                    appLogger.Debug("Events Upload Logger | Started | path: " +  UploadLoggerEvents.path );


                #region commented
                ////// Create the session directory
                //DateTime now = DateTime.Now;
                //Settings._DataStorageDirectory = Settings._MemoryCardDirectory + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");
                //if (!Directory.Exists(Settings._DataStorageDirectory))
                //    Directory.CreateDirectory(Settings._DataStorageDirectory);


                //////Initialize App Logger
                //appLogger = new LocalLogger(Settings._DataStorageDirectory + "\\log", "app_");
                //appLogger.Debug("Starting Application");

                //////Initialize the wockets controller logger
                //Logger.InitLogger(Settings._DataStorageDirectory + "\\log");
                //appLogger.Debug("Session and log directories created.");
                #endregion

                #region commented
                //// Create the session directory
                //DateTime now = DateTime.Now;
                //Settings._DataStorageDirectory = firstCard + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");
                //if (!Directory.Exists(Settings._DataStorageDirectory))
                //    Directory.CreateDirectory(Settings._DataStorageDirectory);

                //appappLogger.InitLogger(Settings._DataStorageDirectory + "\\log\\");   //"\\Wockets\\applog\\");
                //appappLogger.Debug("Starting Application");
                #endregion


            }
            catch(Exception e)
            {
                //appLogger.Error("Exception when trying to create the application directories. Ex: " + e.ToString());
            }

            #endregion


            #region Check shortcuts in the phone startup folder

            //Delete old kernel links
            if (File.Exists("\\Windows\\StartUp\\Kernel.lnk"))
                File.Delete("\\Windows\\StartUp\\Kernel.lnk");

            if (File.Exists("\\Windows\\Start Menu\\Programs\\Detect Activity.lnk"))
                File.Delete("\\Windows\\Start Menu\\Programs\\Detect Activity.lnk");

            if (File.Exists("\\Windows\\StartUp\\Collect Data.lnk"))
                File.Delete("\\Windows\\StartUp\\Collect Data.lnk");

            if (File.Exists("\\Windows\\Start Menu\\Programs\\Collect Data.lnk"))
                File.Delete("\\Windows\\Start Menu\\Programs\\Collect Data.lnk");

            //create wockets app link if it doesn't exist
            if(!File.Exists("\\Windows\\Start Menu\\Programs\\Wockets.lnk"))
                if ( File.Exists(Settings._MainWocketsDirectory + "CollectData.lnk") )
                    File.Copy(Settings._MainWocketsDirectory + "CollectData.lnk", "\\Windows\\Start Menu\\Programs\\Wockets.lnk");

            if ( !File.Exists("\\Windows\\StartUp\\CollectData.lnk"))
               if (File.Exists(Settings._MainWocketsDirectory + "CollectData.lnk"))
                    File.Copy(Settings._MainWocketsDirectory + "CollectData.lnk", "\\Windows\\StartUp\\CollectData.lnk");

            //create QA link if it doesn't exist
            if (File.Exists("\\Windows\\Start Menu\\Programs\\Wockets QA.lnk"))
                File.Delete("\\Windows\\Start Menu\\Programs\\Wockets QA.lnk");
 
            if (!File.Exists("\\Windows\\Start Menu\\Programs\\QA.lnk"))
                if (File.Exists(Settings._MainWocketsDirectory + "WocketsQA.lnk"))
                    File.Copy(Settings._MainWocketsDirectory + "WocketsQA.lnk", "\\Windows\\Start Menu\\Programs\\QA.lnk");

            //create Updater link if doesn't exist
            if (File.Exists("\\Windows\\Start Menu\\Programs\\" + "Wockets Updater.lnk"))
                File.Delete("\\Windows\\Start Menu\\Programs\\Wockets Updater.lnk");

            if( !File.Exists("\\Windows\\Start Menu\\Programs\\Updater.lnk") )
                if ( File.Exists(Settings._MainWocketsDirectory + "Updater.lnk") )
                    File.Copy(Settings._MainWocketsDirectory + "Updater.lnk", "\\Windows\\Start Menu\\Programs\\" + "Updater.lnk");


            #endregion check shortcuts at startup




            #region Read the last sensor set, master list file and app_status


            #region Read the last app status

            try
            {
                if (File.Exists(Settings._MainWocketsDirectory + "\\updater_appstatus.txt"))
                {
                    StreamReader tr_status = new StreamReader(Settings._MainWocketsDirectory + "\\updater_appstatus.txt");
                    this.app_status = tr_status.ReadLine();
                    tr_status.Close();

                    if (this.app_status.CompareTo("") == 0)
                    { this.app_status = "running"; }
                }
                else
                {   //set the default app status
                    this.app_status = "running";
                }
            }
            catch
            {
                this.app_status = "running";
            }

            #endregion


            #region Read the last sensor set

            try
            {
                if (File.Exists(Settings._MainWocketsDirectory + "\\updater_last_set.txt"))
                {
                    StreamReader tr_sensors = new StreamReader(Settings._MainWocketsDirectory + "\\updater_last_set.txt");
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
                if (File.Exists(Settings._MainWocketsDirectory + "\\MasterList.txt"))
                {
                    StreamReader tr_sensors_data = new StreamReader(Settings._MainWocketsDirectory + "\\MasterList.txt");
                    string rline = tr_sensors_data.ReadLine();
                    bool is_IMEI_found = false;

                    while( rline != null & is_IMEI_found== false)
                    {
                        sensor_data = rline.Split(',');
                        if (sensor_data != null & sensor_data.Length == ((int)MasterListParam.Length) )
                        {
                            if (sensor_data[((int)MasterListParam.IMEI)].CompareTo(CurrentPhone._IMEI) == 0)
                            {
                                subjectID = sensor_data[((int)MasterListParam.Subject_ID)];
                                
                                try
                                {
                                    StreamWriter tw = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_id.txt");
                                    tw.WriteLine(CurrentPhone._IMEI);
                                    tw.WriteLine(subjectID);
                                    tw.Flush();
                                    tw.Close();
                                
                                }
                                catch
                                {
                                    appLogger.Debug("Problem writing the user ID to file.");
                                }

                                is_IMEI_found = true;
                            }
                        }
                        else
                            sensor_data = null;

                        rline = tr_sensors_data.ReadLine(); 
                    }

                    tr_sensors_data.Close();

                    if (!is_IMEI_found)
                    {
                        
                        appLogger.Debug("User IMEI not found in master list.");


                        if (File.Exists(Settings._MainWocketsDirectory + "\\updater_id.txt"))
                        {
                            StreamReader tr = new StreamReader(Settings._MainWocketsDirectory + "\\updater_id.txt");
                            string line;

                            if ((line = tr.ReadLine()) != null)
                            {
                                if (line.Trim().Length > 0)
                                {
                                    CurrentPhone._IMEI = rline;
                                    label_phone_IMEI.Text = CurrentPhone._IMEI;

                                    if ((line = tr.ReadLine()) != null)
                                        if (rline.Trim().Length > 0)
                                            subjectID = rline;
                                }
                            }
                            else
                                appLogger.Debug("User IMEI not found in local file updater_id.txt.");
                        }
                        else
                           appLogger.Debug("User IMEI not found in local file updater_id.txt.");
                        
                    }

                }
            }
            catch(Exception e)
            {
                appLogger.Debug("sensor master file couldn't be accessed correctly. Ex: " + e.ToString() );
            }


            #endregion


            #endregion


            #region Initialize the wockets controller (commented)

            //try
            //{
            //    // Create the session directory
            //    DateTime now = DateTime.Now;
            //    Settings._DataStorageDirectory = firstCard + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");
            //    if (!Directory.Exists(Settings._DataStorageDirectory))
            //        Directory.CreateDirectory(Settings._DataStorageDirectory);

            //    //TODO: separate the controller logger from the application one
            //    appLogger.InitLogger(Settings._DataStorageDirectory + "\\log\\");   
            //    appLogger.Debug("Session and log directories created.");


            //    if (wockets_controller != null)
            //    {   wockets_controller.Dispose();
            //        wockets_controller = null;
            //    }
               
            //    wockets_controller = new WocketsController("", "", "");
            //    wockets_controller._StorageDirectory = Settings._DataStorageDirectory;
            //    CurrentWockets._Controller = wockets_controller;
                
            //    appLogger.Debug("Wockets controller initialized.");

            //}
            //catch (Exception e)
            //{
            //    appLogger.Error("Exception when trying to create the application directories. Ex: " + e.ToString());
            //}


            #endregion


            #region commented
            #region Load MAC addresses, locations from sensordata.xml files && match them to the master list (commented)
            //sensors_loaded = LoadSensorsFromMasterList(wockets_controller, sensor_data, this.sensor_set);
            #endregion

            #region Initialize Location Picture  (commented)
            //pictureBox_Location.Image = (Image)Resources.HumanBody;

            ////Assign the parent to the button
            //this.button1.Parent = this.pictureBox_Location;
            //this.button1.BackColor = Color.Transparent;


            //ButtonImList.Images.Add((Image)Resources.buttonIm);
            //ButtonImList.Images.Add((Image)Resources.buttonIm2);
            //ButtonImList.Images.Add((Image)Resources.buttonIm3);
            #endregion
            #endregion


            InitializePanels();


            #region Create thread that tracks the connection status

            ACsUpdateTimer = new System.Windows.Forms.Timer();
            ACsUpdateTimer.Interval = 10000; //update every 10sec
            ACsUpdateTimer.Tick += new EventHandler(ACsUpdateTimer_Tick);
            ACsUpdateTimer.Enabled = false;

            #endregion 


            #region Connection Status Labels
            
            CreateConnectionStatusLabels();
            InitializeConnectionStatusLabels();
            
            #endregion 


            sensors_loaded = false;
            is_change_locations_panel_launched = false;
            sensors_setup_in_panel = false;
                    
            if (app_status.CompareTo("swap") == 0)
            {
                if (InitializeWocketsController())
                {
                    TurnOnPanel(PanelID.PREPARE_SET);
                    swap_event = 1;
                    restart_event = 1;
                }
                else
                    appLogger.Debug("program.cs: The wockets controller was not innitialized correctly. LoadSensors Function returned false.");
            }
            else
            {
                if (InitializeWocketsController())
                {

                    //Load MAC addresses, locations from sensordata.xml files && match them to the master list
                    if (!sensors_loaded)
                        sensors_loaded = LoadSensorsFromMasterList(sensor_data, sensor_set, selected_sensor_locations);

                    if (!ConnetToWocketsController(sensor_set))
                        appLogger.Debug("program.cs: The wockets controller was not innitialized correctly. ConnetToWocketsController Function returned false.");

                    restart_event = 1;
                    Minimize_Main_Window();

                }
                else
                    appLogger.Debug("program.cs: The wockets controller was not innitialized correctly. LoadSensors Function returned false.");

            }



            #region commented
            #region Try to connect sensors to the wockets controller (commneted)

            //if (CurrentWockets._Controller._Sensors.Count > 0 & sensors_loaded)
            //{

            //    #region connect wockets


            //    #region Load The Configuration Xml File

            //    //Load the wockets configuration directory
            //    WocketsConfiguration configuration = new WocketsConfiguration();
            //    configuration.FromXML(Settings._MainWocketsDirectory + "NeededFiles\\Master\\Configuration.xml");

            //    try
            //    {
            //        File.Copy(Settings._MainWocketsDirectory + "NeededFiles\\Master\\Configuration.xml", Settings._DataStorageDirectory + "\\Configuration.xml");
            //    }
            //    catch (Exception e)
            //    {
            //        appLogger.Error("program.cs: Exception when trying to copy the Configuration.xml file to storage card. " + e.ToString());
            //    }

            //    CurrentWockets._Configuration = configuration;

            //    #endregion


            //    //Save the SensorData.Xml to the session data directory
            //    try
            //    {
            //        StreamWriter sensors_data_xml = new StreamWriter(Settings._DataStorageDirectory + "\\SensorData.xml");
            //        sensors_data_xml.Write(wockets_controller.ToXML());
            //        sensors_data_xml.Close();
            //    }
            //    catch (Exception e)
            //    {
            //        appLogger.Error("program.cs: Exception when trying to copy the SensorData.xml file to storage card." + e.ToString());
            //    }


            //    //Set memory mode to local
            //    wockets_controller._Mode = MemoryMode.BluetoothToLocal;

            //    //Initialize wockets controller and set it to "bursty mode"
            //    wockets_controller._TMode = TransmissionMode.Bursty60;

            //    //Initialize pointers to loaded sensors
            //    for (int i = 0; (i < wockets_controller._Sensors.Count); i++)
            //    {
            //        CurrentWockets._Controller._Receivers[i]._ID = i;
            //        CurrentWockets._Controller._Decoders[i]._ID = i;
            //        CurrentWockets._Controller._Sensors[i]._ID = i;
            //        CurrentWockets._Controller._Sensors[i]._Receiver = CurrentWockets._Controller._Receivers[i];
            //        CurrentWockets._Controller._Sensors[i]._Decoder = CurrentWockets._Controller._Decoders[i];
            //        CurrentWockets._Controller._Sensors[i]._Loaded = true;
            //        CurrentWockets._Controller._Sensors[i]._RootStorageDirectory = CurrentWockets._Controller._StorageDirectory + "\\data\\raw\\PLFormat\\";

            //        appLogger.Debug("Program.cs: Sensor Loaded= " + CurrentWockets._Controller._Sensors[i]._Address);
            //    }


            //    #region commented
            //    #region commented
            //    ////Load sensors addresses to array list
            //    //sensors_list = new ArrayList();
            //    //for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
            //    //{
            //    //    sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);
            //    //    appLogger.Debug("Sensor Info Loaded From Xml, Sensor Set: " + sensor_set + "," +
            //    //                 "MAC " + i.ToString() + ":"+ sensors_list[i]);
            //    //}
            //    #endregion

            //    #region Suscribe to Kernel Events (commented)


            //    //SuscribeToKernelEvents();

            //    #endregion
            //    #endregion


            //    #region Initialize thread that tracks the connection status


            //    ACsUpdateTimer = new System.Windows.Forms.Timer();
            //    ACsUpdateTimer.Interval = 10000; //update every 10sec
            //    ACsUpdateTimer.Tick += new EventHandler(ACsUpdateTimer_Tick);
            //    ACsUpdateTimer.Enabled = false;



            //    #region Initialization of Connection Status Variables

            //    PrevFullPkg = new int[wockets_controller._Receivers.Count];
            //    PrevPartialPkg = new int[wockets_controller._Receivers.Count];
            //    PrevEmptyPkg = new int[wockets_controller._Receivers.Count];
            //    LastPkgTime = new DateTime[wockets_controller._Receivers.Count];
            //    ElapsedConnectionTime = new TimeSpan[wockets_controller._Receivers.Count];


            //    #region Initialize the sensor connection status text labels
            //    textBox_sensors_status_0.Visible = false;
            //    textBox_sensors_status_0.Enabled = false;
            //    textBox_sensor_location_0.Visible = false;
            //    textBox_sensor_location_0.Enabled = false;
            //    textBox_sensors_status_1.Visible = false;
            //    textBox_sensors_status_1.Enabled = false;
            //    textBox_sensor_location_1.Visible = false;
            //    textBox_sensor_location_1.Enabled = false;
            //    textBox_sensors_status_2.Visible = false;
            //    textBox_sensors_status_2.Enabled = false;
            //    textBox_sensor_location_2.Visible = false;
            //    textBox_sensor_location_2.Enabled = false;

            //    for (int np = 0; np < wockets_controller._Receivers.Count; np++)
            //    {

            //        //PrevFullPkg[np] = 0;
            //        //PrevPartialPkg[np] = 0;
            //        //PrevEmptyPkg[np] = 0;
            //        //LastPkgTime[np] = DateTime.Now;
            //        //ElapsedConnectionTime[np] = TimeSpan.Zero;


            //        switch (np)
            //        {

            //            case 0:
            //                textBox_sensors_status_0.Visible = true;
            //                textBox_sensors_status_0.Enabled = true;
            //                textBox_sensor_location_0.Visible = true;
            //                textBox_sensor_location_0.Enabled = true;
            //                break;
            //            case 1:
            //                textBox_sensors_status_1.Visible = true;
            //                textBox_sensors_status_1.Enabled = true;
            //                textBox_sensor_location_1.Visible = true;
            //                textBox_sensor_location_1.Enabled = true;
            //                break;
            //            case 2:
            //                textBox_sensors_status_2.Visible = true;
            //                textBox_sensors_status_2.Enabled = true;
            //                textBox_sensor_location_2.Visible = true;
            //                textBox_sensor_location_2.Enabled = true;
            //                break;
            //            default:
            //                break;
            //        }
            //    }
            //    #endregion


            //    #endregion



            //    #region Initialization of upload Status Variables

            //    ElapsedTime_LogUpload = TimeSpan.Zero;
            //    LastLogUploadInvoke = new DateTime();
            //    LastLogUploadInvoke = DateTime.Now;
            //    ElapsedTime_DataUpload = TimeSpan.Zero;

            //    #endregion



            //    #endregion


            //    #region Initialize Elapsed Time Counter On File Upload Screen

            //    //Hide the timer label
            //    textBox_elapsed_time.Visible = false;
            //    textBox_elapsed_time.Enabled = false;
            //    textBox_elapsed_time.Text = "00h:00m:00s";

            //    #endregion


            //    #region Initialize GUI Panels

            //    InitializePanels();
            //    TurnOnPanel(PanelID.CONNECTION);
            //    label_kernel_status.Text = "Loading Application";

            //    #endregion


            //    #region Launch Wockets Controller for Data Collection


            //    //if (CurrentWockets._Controller._Sensors.Count > 0)
            //    //{
            //    try
            //    {
            //        CurrentWockets._Controller.Initialize();
            //        _WocketsRunning = true;
            //        appLogger.Debug("Program.cs: The wockets controller successfully initialized.");

            //        if ( WocketsConnect(_WocketsRunning))
            //        {
            //            //Launch the wocketsQA questionarie program
            //            LaunchWocketsQuestionarie();
            //        }
            //        else
            //        {
            //            //TODO: consolidate this part
            //            TurnOnPanel(PanelID.CONNECTION);
            //            label_kernel_status.Text = "The wockets cannot connect. Please restart the Application.";
            //            Application.DoEvents();

            //            Thread.Sleep(2000);

            //            Application.Exit();
            //            System.Diagnostics.Process.GetCurrentProcess().Kill();
            //        }

            //    }
            //    catch (Exception e)
            //    {
            //        appLogger.Debug("Program.cs: The wockets controller was NOT initialized. Ex:" + e.ToString());

            //        TurnOnPanel(PanelID.CONNECTION);
            //        label_kernel_status.Text = "The wockets controller was NOT initialized. Please restart the Application.";
            //        Application.DoEvents();

            //        Thread.Sleep(2000);

            //        Application.Exit();
            //        System.Diagnostics.Process.GetCurrentProcess().Kill();
            //    }

            //    //}

            //    #endregion Launch Wockets Controller for Data Collection


            //    #endregion connect wockets

            //}
            //else //Sensors Macs not loaded
            //{
            //    #region send error message and quit app

            //    appLogger.Debug("The Sensors Couldn't be loaded. Please restart the Application.");

            //    TurnOnPanel(PanelID.CONNECTION);
            //    label_kernel_status.Text = "The Sensors Couldn't be loaded. Please restart the Application.";
            //    Application.DoEvents();

            //    Thread.Sleep(2000);

            //    Application.Exit();
            //    System.Diagnostics.Process.GetCurrentProcess().Kill();

            //    #endregion

            //}

            #endregion If there are sensors, connect the wockets controller
            #region commented
            #region Try to connect to kernel, (commented)
            //Start the kernel connection sequence
            //StartLoadingWocketsToKernel();
            //appLogger.Debug("Connecting to Kernel in Silent Mode");
            #endregion


            #region Reset Uploader and Received Data Pkgs Counters (commented)

            //ResetUploaderCounters();
            //ResetACsCounters(wockets_controller);

            #endregion
            #endregion 
            #endregion


        }

     #endregion



        private string GetStorageCardName(int TIMEOUT_SECONDS)
        {
            int number_of_trials = -1;
            string firstCard = "";
            System.IO.DirectoryInfo di;
            System.IO.FileSystemInfo[] fsi;

            while (number_of_trials < TIMEOUT_SECONDS)
            {

                di = new System.IO.DirectoryInfo("\\");
                fsi = di.GetFileSystemInfos();

                //iterate through them
                for (int x = 0; x < fsi.Length; x++)
                {
                    //check to see if this is a temporary storage card (e.g. SD card)
                    if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                    {
                        //Verify if is indeed writable
                        firstCard = fsi[x].FullName;
                        try
                        {
                            Directory.CreateDirectory(firstCard + "\\writable");
                            Directory.Delete(firstCard + "\\writable");
                            return firstCard;
                        }
                        catch (Exception)
                        {
                            firstCard = "";
                            Thread.Sleep(1000);
                            continue;
                        }
                        break;
                    }
                }

                number_of_trials++;
            }

            return firstCard;

        }



        private void UpdateDataStorageDirectoryPath()
        {

            // Create the session directory
            DateTime now = DateTime.Now;
            Settings._DataStorageDirectory = Settings._MemoryCardDirectory + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");
            if (!Directory.Exists(Settings._DataStorageDirectory))
                Directory.CreateDirectory(Settings._DataStorageDirectory);


            //Initialize App Logger
            if( appLogger == null)
                appLogger = new LocalLogger(Settings._DataStorageDirectory + "\\log", "app_");
            else
                appLogger.InitLogger(Settings._DataStorageDirectory + "\\log", "app_");
            
            appLogger.Debug("Starting Application");

            //Initialize the wockets controller logger
            Logger.InitLogger(Settings._DataStorageDirectory + "\\log");
            appLogger.Debug("Session and log directories created.");
        }





        #region Location Buttons
        
        public static string NEEDED_FILES_PATH = ""; 
        public static string LOCATION_IMAGES_DIRECTORY = "";
        private List<CustomImageButton> sensor_location_buttons = new List<CustomImageButton>();
        
        //TODO: Adapt this initialization to the total number of sensors
        private int NUMBER_OF_SENSORS = 0;
        private Dictionary<int, string> selected_sensor_locations = new Dictionary<int, string>();
        private Dictionary<int, string> previous_locations = new Dictionary<int, string>();

        private void SetupLocationPanels()
        {

            textBox_location_panel.Location = new Point(1, 0);
            textBox_location_panel.Size = new Size(478, 55);

            panel_location_buttons.Location = new Point(0, 56);
            panel_location_buttons.Size = new Size(480, 570);
            panel_location_buttons.Visible = false;
            panel_location_buttons.Enabled = false;

            panel_sensor_verification_1.Location = new Point(0, 56);
            panel_sensor_verification_1.Size = new Size(480, 570);
            panel_sensor_verification_1.Visible = false;
            panel_sensor_verification_1.Enabled = false;

            textBox_sensor_verification_msg.Location = new Point(40, 87);
            textBox_sensor_verification_msg.Size = new Size(400, 400);

            panel_sensor_verification_2.Location = new Point(0, 0);
            panel_sensor_verification_2.Size = new Size(480, 630);
            panel_sensor_verification_2.Visible = false;
            panel_sensor_verification_2.Enabled = false;

            textBox_location_panel.Text = "Indicate the sensor locations";
            textBox_location_panel.ForeColor = Color.Black;

            buttonLocation_OK.Location = new Point(100, 640);
            buttonLocation_OK.Size = new Size(280, 100);

            Add_LocationButtons();

        }


        private void Add_LocationButtons()
        {
            int _width  = 240;
            int _height = 130;
            int _max_number_buttons = 8;

            int[] _posx = new int[_max_number_buttons];
            int[] _posy = new int[_max_number_buttons];
           
            #region commented
            //_posx[0] = 0;    _posy[0] = 5;      location_id[0] = "";
            //_posx[1] = 240;  _posy[1] = 5;      location_id[1] = "";
            //_posx[2] = 0;    _posy[2] = 145;    location_id[2] = "Right Wrist";
            //_posx[3] = 240;  _posy[3] = 145;    location_id[3] = "Left Wrist";
            //_posx[4] = 0;    _posy[4] = 285;    location_id[4] = "Right Pocket";
            //_posx[5] = 240;  _posy[5] = 285;    location_id[5] = "Left Pocket";
            //_posx[6] = 0;    _posy[6] = 425;    location_id[6] = "Right Ankle";
            //_posx[7] = 240;  _posy[7] = 425;    location_id[7] = "Left Ankle"; 
            #endregion


            _posx[0] = 0;       _posy[0] = 5; 
            _posx[1] = 240;     _posy[1] = 5;
            _posx[2] = 0;       _posy[2] = 135; 
            _posx[3] = 240;     _posy[3] = 135; 
            _posx[4] = 0;       _posy[4] = 265; 
            _posx[5] = 240;     _posy[5] = 265; 
            _posx[6] = 0;       _posy[6] = 395; 
            _posx[7] = 240;     _posy[7] = 395;


            for (int i = 0; i <  _max_number_buttons; i++)
            {
                //create-possition button
                sensor_location_buttons.Add(new CustomImageButton());
                panel_location_buttons.Controls.Add(sensor_location_buttons[i]);
                sensor_location_buttons[i].Parent = this.panel_location_buttons;
                sensor_location_buttons[i].Location = new Point(_posx[i], _posy[i]);
                sensor_location_buttons[i].Size = new Size(_width, _height);
                sensor_location_buttons[i].ForeColor = Color.Gray;
                sensor_location_buttons[i].Click += new EventHandler(location_button_Click);

                //assign images
                if (i == 0 | i == 1)
                {
                    sensor_location_buttons[i].SetButtonActive(false);
                    sensor_location_buttons[i].BackgroundImage = new Bitmap(LOCATION_IMAGES_DIRECTORY + "im_" + (i+1).ToString() + "_clear.jpg");
                    sensor_location_buttons[i].PressedImage    = new Bitmap(LOCATION_IMAGES_DIRECTORY + "im_" + (i+1).ToString() + "_clear.jpg");
                }
                else
                {
                    sensor_location_buttons[i].BackgroundImage = new Bitmap(LOCATION_IMAGES_DIRECTORY + "im_" + (i+1).ToString() + "_unselected.jpg");
                    sensor_location_buttons[i].PressedImage    = new Bitmap(LOCATION_IMAGES_DIRECTORY + "im_" + (i+1).ToString() + "_selected.jpg");
                }


                //assing identifiers
                sensor_location_buttons[i].ID = i;
                sensor_location_buttons[i].Text = "";

                switch (i)
                {
                    case 2:
                        sensor_location_buttons[i].SENSOR_LOCATION = "Right Wrist";
                        //sensor_location_buttons[i].Text = "R." + sensor_location_buttons[i].SENSOR_LOCATION.Substring("Right ".Length);
                        sensor_location_buttons[i].text_aligment = "right";
                        break;
                    case 3:
                        sensor_location_buttons[i].SENSOR_LOCATION = "Left Wrist";
                        //sensor_location_buttons[i].Text = "L." + sensor_location_buttons[i].SENSOR_LOCATION.Substring("Left ".Length);
                        sensor_location_buttons[i].text_aligment = "left";
                        break;
                    case 4:
                        sensor_location_buttons[i].SENSOR_LOCATION = "Right Pocket";
                        //sensor_location_buttons[i].Text = "R." + sensor_location_buttons[i].SENSOR_LOCATION.Substring("Right ".Length);
                        sensor_location_buttons[i].text_aligment = "right";
                        break;
                    case 5:
                        sensor_location_buttons[i].SENSOR_LOCATION = "Left Pocket";
                        //sensor_location_buttons[i].Text = "L." + sensor_location_buttons[i].SENSOR_LOCATION.Substring("Left ".Length);
                        sensor_location_buttons[i].text_aligment = "left";
                        break;
                    case 6:
                        sensor_location_buttons[i].SENSOR_LOCATION = "Right Ankle";
                        //sensor_location_buttons[i].Text = "R." + sensor_location_buttons[i].SENSOR_LOCATION.Substring("Right ".Length);
                        sensor_location_buttons[i].text_aligment = "right";
                        break;
                    case 7:
                        sensor_location_buttons[i].SENSOR_LOCATION = "Left Ankle";
                        //sensor_location_buttons[i].Text = "L." + sensor_location_buttons[i].SENSOR_LOCATION.Substring("Left ".Length);
                        sensor_location_buttons[i].text_aligment = "left";
                        break;
                    default :
                            sensor_location_buttons[i].SENSOR_LOCATION = "";
                        break;
                }
            
            }

            #region commented
            //sensor_location_buttons[0].Click += new EventHandler(location_button_Click);
            //sensor_location_buttons[1].Click += new EventHandler(location_button_Click);
            //sensor_location_buttons[2].Click += new EventHandler(location_button_Click);
            //sensor_location_buttons[3].Click += new EventHandler(location_button_Click);
            //sensor_location_buttons[4].Click += new EventHandler(location_button_Click);
            //sensor_location_buttons[5].Click += new EventHandler(location_button_Click);
            #endregion

        }


        private void Dispose_LocationButtons()
        {

            for (int i = 0; i < sensor_location_buttons.Count; i++)
                sensor_location_buttons[i].Dispose();

        }



        //Click on body location buttons
        private void location_button_Click(object sender, EventArgs e)
        {
            panel_location_buttons.Enabled = false;

            NUMBER_OF_SENSORS = GetNumberOfSelectedLocations();
            PostLocationPanelButtonsMsg(NUMBER_OF_SENSORS);

            panel_location_buttons.Enabled = true;
        }


        private void PrepareSensorSet()
        {

            if (sensor_set.CompareTo("red") == 0)
                panel_sensor_verification_1.BackColor = Color.Tomato;
            else if (sensor_set.CompareTo("green") == 0)
                panel_sensor_verification_1.BackColor = Color.YellowGreen;

            textBox_location_panel.Text = "";
            textBox_location_panel.Visible = false;
            textBox_location_panel.ForeColor = Color.Black;
            textBox_sensor_verification_msg.Text = "PREPARE\r\n\r\n" + sensor_set.ToUpper() + "\r\n\r\nSENSORS";

            buttonLocation_OK.Enabled = true;
            buttonLocation_OK.Visible = true;
            buttonLocation_OK.Text = "OK";

            menuMainAppActions.Text = "Change Set";
            menuQuitApp.Text = "";

        }


        private int GetNumberOfSelectedLocations()
        {
            int sensor_count = 0;

            if (sensor_location_buttons != null)
            {
                for (int i = 0; i < sensor_location_buttons.Count; i++)
                {
                    if (sensor_location_buttons[i].IsButtonActive())
                        if (sensor_location_buttons[i].pressed)
                            sensor_count++;
                }
            }

            return sensor_count;
        }


        private void PostLocationPanelButtonsMsg(int sensors_count)
        {
            textBox_location_panel.Visible = true;

            if (sensors_count == 0)
            {
                textBox_location_panel.Text = "Indicate the sensor locations";
                textBox_location_panel.ForeColor = Color.Black;
                buttonLocation_OK.Enabled = false;
            }
            else if (sensors_count == 1)
            {
                textBox_location_panel.Text = "Indicate the sensor locations";
                textBox_location_panel.ForeColor = Color.Black;
                buttonLocation_OK.Enabled = true;
            }
            else if (sensors_count == 2)
            {
                textBox_location_panel.Text = "Press OK when done";
                textBox_location_panel.ForeColor = Color.Green;
                buttonLocation_OK.Enabled = true;
            }
            else if (sensors_count == -1)
            {
                textBox_location_panel.Text = "Locations were NOT modified";
                textBox_location_panel.ForeColor = Color.Red;
                buttonLocation_OK.Enabled = true;
            }
            else
            {
                textBox_location_panel.Text = "Select maximum TWO locations";
                textBox_location_panel.ForeColor = Color.Tomato;
                buttonLocation_OK.Enabled = false;
            }

        }


        private int GetSelectedLocationsFromPanel()
        {
           selected_sensor_locations.Clear();

            for (int i = 0; i < sensor_location_buttons.Count; i++)
            {
                if (sensor_location_buttons[i].IsButtonActive() & sensor_location_buttons[i].pressed)
                {
                    if (sensor_location_buttons[i].SENSOR_LOCATION.Length > 0)
                      selected_sensor_locations.Add(selected_sensor_locations.Count, sensor_location_buttons[i].SENSOR_LOCATION);
                }
            }

            return selected_sensor_locations.Count;
        }


        private int GetSelectedLocationsFromController()
        {
            selected_sensor_locations.Clear();

            if( CurrentWockets._Controller != null)
                if( CurrentWockets._Controller._Sensors != null)
                    for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
                    {
                        if (CurrentWockets._Controller._Sensors[i]._Location.CompareTo("null") != 0)
                            selected_sensor_locations.Add(selected_sensor_locations.Count, CurrentWockets._Controller._Sensors[i]._Location);
                    }

            return selected_sensor_locations.Count;
        }



        bool is_change_locations_panel_launched = false;
        bool sensors_setup_in_panel = false;



        private void buttonLocation_OK_Click(object sender, EventArgs e)
        {
            buttonLocation_OK.Enabled = false;

            if (panel_sensor_verification_1.Visible)
            {

                if( textBox_sensor_verification_msg.Text.Contains("SWAP") )
                {
                    // finish setting up the sensors set id and locations, consequently,
                    // connect to the controller for fist time
                    panel_sensor_verification_1.Visible = false;
                    panel_sensor_verification_1.Enabled = false;
                    buttonLocation_OK.Enabled = false;
                    buttonLocation_OK.Visible = false;
                    Application.DoEvents();


                    CurrentPanel = PanelID.LOCATION;


                    #region commented 
                        ////Load MAC addresses, locations from sensordata.xml files && match them to the master list
                    //if (!sensors_loaded)
                    //    sensors_loaded = LoadSensorsFromMasterList(sensor_data, this.sensor_set, selected_sensor_locations);


                    //if (sensors_loaded)
                    //{

                    //    #region commented
                    //    //for (int i = 0; i < wockets_controller._Sensors.Count; i++)
                    //    //{
                    //    //    if (i < selected_sensor_locations.Count)
                    //    //        wockets_controller._Sensors[i]._Location = selected_sensor_locations[i];
                    //    //    else
                    //    //        wockets_controller._Sensors[i]._Location = "null";

                    //        #region commented
                    //        //{
                    //        //wockets_controller._Sensors.Remove(i);
                    //        //if (i < wockets_controller._Receivers.Count) 
                    //        //  wockets_controller._Receivers.Remove(i);
                    //        //if (i < wockets_controller._Decoders.Count ) 
                    //        //  wockets_controller._Decoders.Remove(i);
                    //        //}
                    //        #endregion

                    //        #region commented for now
                    //        //for (int j = 0; j < selected_sensor_locations.Count; j++)
                    //        //{     
                    //        #region commented
                    //        //if ( selected_locations[j,1].Contains(i.ToString()))
                    //        //{
                    //        //    wockets_controller._Sensors[i]._Location = selected_locations[j, 0];
                    //        //    break;
                    //        //}
                    //        #endregion

                    //        //if (i == j)
                    //        //{
                    //        //   wockets_controller._Sensors[i]._Location = selected_sensor_locations[j];
                    //        //break;
                    //        //}
                    //        //}
                    //        #endregion
                    //    //}
                    //    #endregion 

                    //    #region Save selected locations to local xml file (commented)
                    //    //string xml_filename = "";
                    //    //try
                    //    //{   
                    //    //    if (sensor_set.CompareTo("red") == 0)
                    //    //        xml_filename = "\\updater_SensorData1.xml";
                    //    //    else
                    //    //        xml_filename = "\\updater_SensorData2.xml";

                    //    //    StreamWriter sensors_data_xml = new StreamWriter(Settings._MainWocketsDirectory + xml_filename);
                    //    //    sensors_data_xml.Write(wockets_controller.ToXML());
                    //    //    sensors_data_xml.Close();
                    //    //}
                    //    //catch (Exception ex)
                    //    //{
                    //    //    appLogger.Error("program.cs: Exception when trying to save sensor data to the " + xml_filename + ". SetID: " + sensor_set + ". EX:" + ex.ToString());
                    //    //}
                    //    #endregion 

                    //     SaveSensorDataToXml(sensor_set);
                    //     ConnetToWocketsController();

                    //     //menuMainAppActions.Text = "Minimize";
                    //     //menuQuitApp.Text = "Settings";

                    //}
                    //else
                    //    appLogger.Error("program.cs: Sensors not loaded correctly. LoadSensors Function returned false.");

                    #endregion         
                    

                    if( !UpdateSensorLocations( selected_sensor_locations) )
                        appLogger.Debug("program.cs: the locations were not updated.");

                    if (!ConnetToWocketsController(sensor_set))
                            appLogger.Debug("program.cs: The wockets controller was not innitialized correctly. ConnetToWocketsController Function returned false.");

                    is_change_locations_panel_launched = false;
                    sensors_setup_in_panel = false;

                    Minimize_Main_Window();

                }
                else if (textBox_sensor_verification_msg.Text.Contains("LOCATION"))
                {
                    //update # of sensors and sensor locations and reconect controller
                    panel_sensor_verification_1.Visible = false;
                    panel_sensor_verification_1.Enabled = false;
                    buttonLocation_OK.Enabled = false;
                    buttonLocation_OK.Visible = false;
                    Application.DoEvents();

                    CurrentPanel = PanelID.LOCATION;

                    Disconnect_WocketsController();
                    Thread.Sleep(500);

                    
                    ////Update Session Directory
                    //DateTime now = DateTime.Now;
                    //Settings._DataStorageDirectory = Settings._MemoryCardDirectory + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");
                    //if (!Directory.Exists(Settings._DataStorageDirectory))
                    //    Directory.CreateDirectory(Settings._DataStorageDirectory);


                    ////Initialize App Logger
                    //appLogger.InitLogger(Settings._DataStorageDirectory + "\\log", "app_");
                    //appLogger.Debug("Disconnecting/Reconnecting Wockets");

                    ////Initialize the wockets controller logger
                    //Logger.InitLogger(Settings._DataStorageDirectory + "\\log");
                    //appLogger.Debug("Session and log directories created.");


                    UpdateDataStorageDirectoryPath();


                    if (InitializeWocketsController())
                    {
                        //Load MAC addresses, locations from sensordata.xml files && match them to the master list
                        if (!sensors_loaded)
                            sensors_loaded = LoadSensorsFromMasterList(sensor_data, sensor_set, selected_sensor_locations);


                        if (!ConnetToWocketsController(sensor_set))
                            appLogger.Debug("program.cs: The wockets controller was not innitialized correctly. ConnetToWocketsController Function returned false.");

                        is_change_locations_panel_launched = false;
                        sensors_setup_in_panel = false;
                    }
                    else
                        appLogger.Debug("program.cs: The wockets controller was not innitialized correctly. LoadSensors Function returned false.");

              
                }
                else
                {
                    //Set locations after specify sensor set
                    GoToPanel(PanelID.PREPARE_SET, PanelID.LOCATION_BUTTONS);
                    menuMainAppActions.Text = "Back";
                    menuQuitApp.Text = "";
                }

            }
            else if (panel_location_buttons.Visible)
            {
                NUMBER_OF_SENSORS = GetSelectedLocationsFromPanel();

                //Finish selecting the locations
                if (menuMainAppActions.Text.CompareTo("Cancel") == 0)
                {
                    #region commented
                    //previous_locations.Clear();
                    //if( selected_sensor_locations != null)
                    //    for (int i = 0; i < selected_sensor_locations.Count; i++)
                    //        previous_locations.Add(i,selected_sensor_locations[i]);

                    //int nlocations = GetSelectedLocationsIDs();
                    //NUMBER_OF_SENSORS = GetSelectedLocationsFromPanel();

                    #endregion 
                   
                    //Determine if the previous locations have changed
                    if (selected_sensor_locations.Count > 0)
                    {
                        bool is_different = false;

                        if (NUMBER_OF_SENSORS != previous_locations.Count)
                            is_different = true;
                        else 
                        {
                            for (int i = 0; i < selected_sensor_locations.Count; i++)
                            {
                                if (selected_sensor_locations[i].CompareTo(previous_locations[i]) != 0)
                                {
                                    is_different = true;
                                    break;
                                }
                            }
                        }


                        if (is_different)
                        {
                           //If the # of sensors selected is valid, go to panel W
                            if (NUMBER_OF_SENSORS == 1 || NUMBER_OF_SENSORS == 2)
                            {
                                GoToPanel(PanelID.LOCATION_BUTTONS, PanelID.VERIFY_W_SENSOR);
                                menuMainAppActions.Text = "Back";
                                menuQuitApp.Text = "";
                            }
                            else
                                PostLocationPanelButtonsMsg(NUMBER_OF_SENSORS);
                        }
                        else
                        { 
                           //Notify that the sensors locations didn't change
                            PostLocationPanelButtonsMsg(-1);
                        }
                    }
                    else
                    {
                        PostLocationPanelButtonsMsg(NUMBER_OF_SENSORS);
                    }

                }
                else
                {
                    if (NUMBER_OF_SENSORS == 1 || NUMBER_OF_SENSORS == 2)
                    {
                        GoToPanel(PanelID.LOCATION_BUTTONS, PanelID.VERIFY_W_SENSOR);
                        menuMainAppActions.Text = "Back";
                        menuQuitApp.Text = "";
                    }
                    else
                        PostLocationPanelButtonsMsg(NUMBER_OF_SENSORS);
                }

            }
            else if( panel_sensor_verification_2.Visible)
            {
                if ( (panel_sensor_verification_labelID.Text.CompareTo("W") == 0) & NUMBER_OF_SENSORS == 2)
                    GoToPanel(PanelID.VERIFY_W_SENSOR, PanelID.VERIFY_A_SENSOR);
                else
                    GoToPanel(PanelID.VERIFY_A_SENSOR, PanelID.SWAP_COMPLETED);
            }
        }


        private void GoToLocationButton_Click(object sender, EventArgs e)
        {
            GoToLocationButton.Enabled = false;

            menuQuitApp.Text = "";
            menuMainAppActions.Text = "Cancel";
            is_change_locations_panel_launched = true;
            GoToPanel(PanelID.SETTINGS_OPTIONS,PanelID.LOCATION_BUTTONS);

            GoToLocationButton.Enabled = true;
        
        }


        #region commented
        //private Bitmap MakeBitmap(Color color, int width, int height)
        //{
        //    Bitmap bmp = new Bitmap(width, height);
        //    Graphics g = Graphics.FromImage(bmp);
        //    g.FillRectangle(new SolidBrush(color), 0, 0, bmp.Width, bmp.Height);
        //    g.DrawEllipse(new Pen(Color.DarkGray), 3, 3, width - 6, height - 6);
        //    g.Dispose();

        //    return bmp;
        //}
        #endregion


        #endregion


        #region Set Panels ON/OFF

            private PanelID LastPanel = PanelID.NONE;
            private PanelID CurrentPanel = PanelID.NONE;

            private void InitializePanels()
            {
                //Settings panels
                SettingsPanel.Visible = false;
                SettingsPanel.Enabled = false;

                PanelSettingsOptions.Visible = false;
                PanelSettingsOptions.Enabled = false;

                PanelSettingsDetailed.Visible = false;
                PanelSettingsDetailed.Enabled = false;


                //Main Sensors Status
                SwapPanel.Visible = false;
                SwapPanel.Enabled = false;

                UploadDataPanel.Visible = false;
                UploadDataPanel.Enabled = false;

                SensorPacketsPanel.Visible = false;
                SensorPacketsPanel.Enabled = false;


                //Connection Status
                ConnectPanel.Visible = false;
                ConnectPanel.Enabled = false;

                panel_blank.Visible = false;
                panel_blank.Enabled = false;

                ElapsedTimePanel.Visible = false;
                ElapsedTimePanel.Enabled = false;


                //Location sub-panels
                LocationPanel.Visible = false;
                LocationPanel.Enabled = false;

                panel_location_buttons.Visible = false;
                panel_location_buttons.Enabled = false;

                panel_sensor_verification_1.Visible = false;
                panel_sensor_verification_1.Enabled = false;

                panel_sensor_verification_2.Visible = false;
                panel_sensor_verification_2.Enabled = false;


                SetupLocationPanels();

            }


            private void TurnOnPanel(PanelID ID)
            {

                #region TurnOff CurrentPanel & Update LastPanelSet variable


                switch (CurrentPanel)
                {
                    case PanelID.SWAP:
                        SwapPanel.Visible = false;
                        SwapPanel.Enabled = false;
                        break;

                    case PanelID.SETTINGS:
                        SettingsPanel.Visible = false;
                        SettingsPanel.Enabled = false;
                        break;

                    case PanelID.SETTINGS_OPTIONS:
                        SettingsPanel.Visible = false;
                        SettingsPanel.Enabled = false;

                        PanelSettingsOptions.Visible = false;
                        PanelSettingsOptions.Enabled = false;
                        break;

                    case PanelID.SETTINGS_DETAILS:
                        SettingsPanel.Visible = false;
                        SettingsPanel.Enabled = false;

                        PanelSettingsDetailed.Visible = false;
                        PanelSettingsDetailed.Enabled = false;
                        break;

                    case PanelID.UPLOAD:
                        UploadDataPanel.Visible = false;
                        UploadDataPanel.Enabled = false;

                        //Stop Update Thread For Data Upload
                        StopUpdateUploadThread();
                        //textBox_elapsed_time.Visible = false;
                        break;

                    case PanelID.PACKETS:
                        SensorPacketsPanel.Visible = false;
                        SensorPacketsPanel.Enabled = false;
                        break;

                    case PanelID.CONNECTION:
                        ConnectPanel.Visible = false;
                        ConnectPanel.Enabled = false;
                        break;

                    case PanelID.LOCATION:
                        LocationPanel.Visible = false;
                        LocationPanel.Visible = false;
                        break;

                    case PanelID.PREPARE_SET:
                        panel_sensor_verification_1.Visible = false;
                        panel_sensor_verification_1.Enabled = false;

                        textBox_location_panel.Text = "";
                        textBox_location_panel.Visible = false;
                        buttonLocation_OK.Enabled = false;
                        break;

                    case PanelID.LOCATION_BUTTONS:
                        panel_location_buttons.Visible = false;
                        panel_location_buttons.Enabled = false;
                        textBox_location_panel.Text = "";
                        textBox_location_panel.Visible = false;
                        buttonLocation_OK.Enabled = false;

                        if (menuMainAppActions.Text.CompareTo("Cancel") == 0)
                        {
                            LocationPanel.Visible = false;
                            LocationPanel.Enabled = false;
                        }
                        break;

                    case PanelID.VERIFY_W_SENSOR:
                        panel_sensor_verification_2.Visible = false;
                        panel_sensor_verification_2.Enabled = false;

                        panel_sensor_verification_labelID.Text = "";
                        panel_sensor_verification2_label_step.Text = "";
                        panel_location_sensorID_main_label.Text = "";
                        break;

                    case PanelID.VERIFY_A_SENSOR:
                        panel_sensor_verification_2.Visible = false;
                        panel_sensor_verification_2.Enabled = false;

                        panel_sensor_verification_labelID.Text = "";
                        panel_sensor_verification2_label_step.Text = "";
                        panel_location_sensorID_main_label.Text = "";
                        break;

                    case PanelID.SWAP_COMPLETED:
                        panel_sensor_verification_1.Visible = false;
                        panel_sensor_verification_1.Enabled = false;

                        textBox_location_panel.Text = "";
                        textBox_location_panel.Visible = false;
                        buttonLocation_OK.Enabled = false;
                        break;

                    default:
                        break;
                }

                LastPanel = CurrentPanel;

                #endregion


                #region Transition to new panel

                if (ID == PanelID.LOCATION )
                {
                    ElapsedTimePanel.Visible = false;
                    ElapsedTimePanel.Enabled = false;
                    ElapsedTimePanel.SendToBack();

                    panel_blank.BringToFront();
                    panel_blank.Visible = true;
                    Application.DoEvents();
                    Thread.Sleep(50);
                    panel_blank.Visible = false;

                }
                else if (ID == PanelID.PREPARE_SET | ID == PanelID.LOCATION_BUTTONS |
                         ID == PanelID.VERIFY_W_SENSOR | ID == PanelID.VERIFY_A_SENSOR |
                         ID == PanelID.SWAP_COMPLETED)
                {
                    Application.DoEvents();
                }
                else if( ID != PanelID.NONE )
                {
                    ElapsedTimePanel.Visible = true;
                    ElapsedTimePanel.Enabled = true;
                    ElapsedTimePanel.BringToFront();

                    panel_blank.BringToFront();
                    panel_blank.Visible = true;
                    Application.DoEvents();
                    Thread.Sleep(50);
                    panel_blank.Visible = false;

                }




                #endregion


                #region TurnOn Requested Panel & Update CurrentPanelSet variable

                switch (ID)
                {
                    case PanelID.SWAP:
                        SwapPanel.BringToFront();
                        SwapPanel.Visible = true;
                        SwapPanel.Enabled = true;

                        menuMainAppActions.Text = "Minimize";
                        menuQuitApp.Text = "Options"; 

                        break;

                    case PanelID.SETTINGS:
                        SettingsPanel.Visible = true;
                        SettingsPanel.Enabled = true;
                        SettingsPanel.BringToFront();
                        break;

                    case PanelID.SETTINGS_OPTIONS:
                        SettingsPanel.Visible = true;
                        SettingsPanel.Enabled = true;
                        SettingsPanel.BringToFront();

                        PanelSettingsOptions.Visible = true;
                        PanelSettingsOptions.Enabled = true;
                        PanelSettingsOptions.BringToFront();

                        menuMainAppActions.Text = "Home";
                        menuQuitApp.Text = "Settings";
                        break;

                    case PanelID.SETTINGS_DETAILS:
                        SettingsPanel.Visible = true;
                        SettingsPanel.Enabled = true;
                        SettingsPanel.BringToFront();

                        PanelSettingsDetailed.Visible = true;
                        PanelSettingsDetailed.Enabled = true;
                        PanelSettingsDetailed.BringToFront();

                        menuMainAppActions.Text = "Back";
                        menuQuitApp.Text = "Quit";
                        break;

                    case PanelID.UPLOAD:
                        //Launch the update thread for the data upload
                        //textBox_elapsed_time.Visible = true;
                        StartUpdateUploadThread();

                        UploadDataPanel.BringToFront();
                        UploadDataPanel.Visible = true;
                        UploadDataPanel.Enabled = true;
                        break;

                    case PanelID.PACKETS:
                        SensorPacketsPanel.BringToFront();
                        SensorPacketsPanel.Visible = true;
                        SensorPacketsPanel.Enabled = true;
                        break;

                    case PanelID.CONNECTION:
                        ConnectPanel.BringToFront();
                        ConnectPanel.Visible = true;
                        ConnectPanel.Enabled = true;
                        break;

                    case PanelID.LOCATION:
                        PrepareSensorSet();
                        panel_sensor_verification_1.Visible = true;
                        panel_sensor_verification_1.Enabled = true;
                        panel_sensor_verification_1.BringToFront();

                        LocationPanel.BringToFront();
                        LocationPanel.Visible = true;
                        LocationPanel.Enabled = true;
                        break;

                    case PanelID.PREPARE_SET:
                        LocationPanel.Visible = true;
                        LocationPanel.Enabled = true;
                        LocationPanel.BringToFront();

                        PrepareSensorSet();
                        panel_sensor_verification_1.Visible = true;
                        panel_sensor_verification_1.Enabled = true;
                        panel_sensor_verification_1.BringToFront();

                        buttonLocation_OK.Enabled = true;
                        buttonLocation_OK.Text = "OK";

                        break;

                    case PanelID.LOCATION_BUTTONS:

                        LocationPanel.Visible = true;
                        LocationPanel.Enabled = true;
                        LocationPanel.BringToFront();


                        if (!sensors_setup_in_panel)
                        {

                            //If not loaded, load MAC addresses and locations from sensordata.xml files && match them to the master list
                            if (!sensors_loaded)
                                sensors_loaded = LoadSensorsFromMasterList(sensor_data, sensor_set, selected_sensor_locations);

                            if (sensors_loaded)
                            {
                                NUMBER_OF_SENSORS = GetSelectedLocationsFromController();
                                sensors_setup_in_panel = true;

                                //save the previous locations
                                previous_locations.Clear();
                                if (selected_sensor_locations != null)
                                    for (int i = 0; i < selected_sensor_locations.Count; i++)
                                        previous_locations.Add(i, selected_sensor_locations[i]);


                                //set buttons values according with the selected locations
                                for (int i = 0; i < sensor_location_buttons.Count; i++)
                                {
                                    bool is_selected = false;

                                    for (int j = 0; j < selected_sensor_locations.Count; j++)
                                    {
                                        if (sensor_location_buttons[i].IsButtonActive())
                                            if (sensor_location_buttons[i].SENSOR_LOCATION.CompareTo(selected_sensor_locations[j]) == 0)
                                            {
                                                is_selected = true;
                                                break;
                                            }
                                    }


                                    if (is_selected)
                                        sensor_location_buttons[i].pressed = true;
                                    else
                                        sensor_location_buttons[i].pressed = false;
                                }
                            }
                            else
                                appLogger.Debug("Launching the location buttons panel: sensors not loaded.");
                        }
                        else
                        {
                            //NUMBER_OF_SENSORS = GetNumberOfSelectedLocations();
                            NUMBER_OF_SENSORS = GetSelectedLocationsFromPanel();
                        }
                

                        PostLocationPanelButtonsMsg(NUMBER_OF_SENSORS);

                        panel_location_buttons.Visible = true;
                        panel_location_buttons.Enabled = true;
                        panel_location_buttons.BringToFront();

                        buttonLocation_OK.Visible = true;
                        buttonLocation_OK.Text = "OK";

                        break;

                    case PanelID.VERIFY_W_SENSOR:

                        LocationPanel.Visible = true;
                        LocationPanel.Enabled = true;
                        LocationPanel.BringToFront();

                        //Indicate the W sensor placement
                        //int nlocations = GetSelectedLocationsFromPanel();

                        if (NUMBER_OF_SENSORS == 1 | NUMBER_OF_SENSORS == 2)
                        {
                            string enclosure_type = "strap";
                            if ( selected_sensor_locations[0].Contains("Pocket"))
                                enclosure_type = "pouch";

                            panel_sensor_verification2_label_step.Text = "STEP ONE";
                            panel_sensor_verification_labelID.Text = "W";
                            panel_location_sensorID_main_label.Text = "1.  Place the " + "W" + " sensor in\r\n " +
                                                                      "    the " + enclosure_type + ". \r\n\r\n" +
                                                                      "2.  Then, put the " + enclosure_type + " on your \r\n " +
                                                                      "    " + selected_sensor_locations[0].ToUpper() + ".\r\n\r\n " +
                                                                      "3.  When done, tap OK.";


                            if (sensor_set.CompareTo("red") == 0)
                                panel_sensor_verification_labelID.BackColor = Color.Tomato;
                            else if (sensor_set.CompareTo("green") == 0)
                                panel_sensor_verification_labelID.BackColor = Color.YellowGreen;


                            buttonLocation_OK.Enabled = true;


                            panel_sensor_verification_2.Visible = true;
                            panel_sensor_verification_2.Enabled = true;
                            panel_sensor_verification_2.BringToFront();

                        }
                        else
                        {
                            textBox_location_panel.Text = "Verify the sensors location";
                            textBox_location_panel.ForeColor = Color.Tomato;
                            buttonLocation_OK.Enabled = true;

                            //NUMBER_OF_SENSORS = GetNumberOfSelectedLocations();

                            panel_location_buttons.Visible = true;
                            panel_location_buttons.Enabled = true;
                            panel_location_buttons.BringToFront();
                        }

                        buttonLocation_OK.Text = "OK";

                        break;

                    case PanelID.VERIFY_A_SENSOR:

                        LocationPanel.Visible = true;
                        LocationPanel.Enabled = true;
                        LocationPanel.BringToFront();

                        if (NUMBER_OF_SENSORS == 2)
                        {
                            string enclosure_type = "strap";
                            if (selected_sensor_locations[1].Contains("Pocket"))
                                enclosure_type = "pouch";

                            panel_sensor_verification2_label_step.Text = "STEP TWO";
                            panel_sensor_verification_labelID.Text = "A";
                            panel_location_sensorID_main_label.Text = "1.  Place the " + "A" + " sensor in\r\n " +
                                                                      "    the " + enclosure_type + ". \r\n\r\n" +
                                                                      "2.  Then, put the " + enclosure_type + " on your\r\n " +
                                                                      "    " + selected_sensor_locations[1].ToUpper() + ".\r\n\r\n " +
                                                                      "3.  When done, tap OK.";


                            panel_sensor_verification_2.Visible = true;
                            panel_sensor_verification_2.Enabled = true;
                            panel_sensor_verification_2.BringToFront();

                            buttonLocation_OK.Enabled = true;

                        }
                        else
                        {
                            //----------------------------------
                            // TODO: Goto locations panel
                            //----------------------------------
                            textBox_location_panel.Text = "Verify the sensors location";
                            textBox_location_panel.ForeColor = Color.Tomato;
                            buttonLocation_OK.Enabled = true;
                            
                            //LastPanel =
                            //NUMBER_OF_SENSORS = GetNumberOfSelectedLocations();

                            panel_location_buttons.Visible = true;
                            panel_location_buttons.Enabled = true;
                            panel_location_buttons.BringToFront();


                            #region commented
                            //textBox_location_panel.Text = "Verify the sensors location";
                            //textBox_location_panel.ForeColor = Color.Tomato;
                            //buttonLocation_OK.Enabled = true;
                            ////NUMBER_OF_SENSORS = GetNumberOfSelectedLocations();
                            //panel_location_buttons.Visible = true;
                            //panel_location_buttons.Enabled = true;
                            //panel_location_buttons.BringToFront();
                            #endregion 
                            
                        }

                        buttonLocation_OK.Text = "OK";

                        break;

                    case PanelID.SWAP_COMPLETED:

                        LocationPanel.Visible = true;
                        LocationPanel.Enabled = true;
                        LocationPanel.BringToFront();

                        panel_sensor_verification_1.Visible = true;
                        panel_sensor_verification_1.Enabled = false;
                        panel_sensor_verification_1.BackColor = Color.White;

                        if (is_change_locations_panel_launched)
                        {
                            if( NUMBER_OF_SENSORS > 1)
                                textBox_sensor_verification_msg.Text = "SENSOR\r\nLOCATIONS\r\nMODIFIED";
                            else
                                textBox_sensor_verification_msg.Text = "SENSOR\r\nLOCATION\r\nMODIFIED";

                            buttonLocation_OK.Text = "OK"; 
                        }
                        else
                        {
                            textBox_sensor_verification_msg.Text = "SWAP\r\nCOMPLETED\r\nTHANKS!";
                            buttonLocation_OK.Text = "OK"; 
                        }

                        buttonLocation_OK.Enabled = true;

                        break;


                    default:
                        break;
                }

                CurrentPanel = ID;

                #endregion

            }


            private void GoToPanel(PanelID current_panel, PanelID next_panel)
            {
                CurrentPanel = current_panel;
                TurnOnPanel(next_panel);
            }


            private void CreateConnectionStatusLabels()
            {
                
                PrevFullPkg = new int[MAX_NUMBER_OF_SENSORS];
                PrevPartialPkg = new int[MAX_NUMBER_OF_SENSORS];
                PrevEmptyPkg = new int[MAX_NUMBER_OF_SENSORS];
                LastPkgTime = new DateTime[MAX_NUMBER_OF_SENSORS];
                ElapsedConnectionTime = new TimeSpan[MAX_NUMBER_OF_SENSORS];
            }


            private void InitializeConnectionStatusLabels()
            {


                #region Initialize the sensor packets status text labels

                //Text Labels for sensor 0
                textBox_sensors_status_0.Visible = false;
                textBox_sensors_status_0.Enabled = false;
                textBox_sensor_location_0.Visible = false;
                textBox_sensor_location_0.Enabled = false;
                textBox_sensor_ID_0.Visible = false;
                textBox_sensor_ID_0.Enabled = false;

                textBox_spanel_sensors_location_0.Visible = false;
                textBox_spanel_sensors_location_0.Enabled = false;
                textBox_spanel_ac_full_0.Visible = false;
                textBox_spanel_ac_full_0.Enabled = false;
                textBox_spanel_ac_full_0_label.Visible = false;
                textBox_spanel_ac_full_0_label.Enabled = false;
                textBox_spanel_ac_last_0.Visible = false;
                textBox_spanel_ac_last_0.Enabled = false;
                textBox_spanel_ac_last_0_label.Visible = false;
                textBox_spanel_ac_last_0_label.Enabled = false;
                textBox_spanel_ac_new_0.Visible = false;
                textBox_spanel_ac_new_0.Enabled = false;
                textBox_spanel_ac_new_0_label.Visible = false;
                textBox_spanel_ac_new_0_label.Enabled = false;
                textBox_spanel_ac_partial_0.Visible = false;
                textBox_spanel_ac_partial_0.Enabled = false;
                textBox_spanel_ac_partial_0_label.Visible = false;
                textBox_spanel_ac_partial_0_label.Enabled = false;
                textBox_spanel_ac_empty_0.Visible = false;
                textBox_spanel_ac_empty_0.Enabled = false;
                textBox_spanel_ac_empty_0_label.Visible = false;
                textBox_spanel_ac_empty_0_label.Enabled = false;



                //Text Labels for sensor 1
                textBox_sensors_status_1.Visible = false;
                textBox_sensors_status_1.Enabled = false;
                textBox_sensor_location_1.Visible = false;
                textBox_sensor_location_1.Enabled = false;
                textBox_sensor_ID_1.Visible = false;
                textBox_sensor_ID_1.Enabled = false;


                textBox_spanel_sensors_location_1.Visible = false;
                textBox_spanel_sensors_location_1.Enabled = false;
                textBox_spanel_ac_full_1.Visible = false;
                textBox_spanel_ac_full_1.Enabled = false;
                textBox_spanel_ac_full_1_label.Visible = false;
                textBox_spanel_ac_full_1_label.Enabled = false;
                textBox_spanel_ac_last_1.Visible = false;
                textBox_spanel_ac_last_1.Enabled = false;
                textBox_spanel_ac_last_1_label.Visible = false;
                textBox_spanel_ac_last_1_label.Enabled = false;
                textBox_spanel_ac_new_1.Visible = false;
                textBox_spanel_ac_new_1.Enabled = false;
                textBox_spanel_ac_new_1_label.Visible = false;
                textBox_spanel_ac_new_1_label.Enabled = false;
                textBox_spanel_ac_partial_1.Visible = false;
                textBox_spanel_ac_partial_1.Enabled = false;
                textBox_spanel_ac_partial_1_label.Visible = false;
                textBox_spanel_ac_partial_1_label.Enabled = false;
                textBox_spanel_ac_empty_1.Visible = false;
                textBox_spanel_ac_empty_1.Enabled = false;
                textBox_spanel_ac_empty_1_label.Visible = false;
                textBox_spanel_ac_empty_1_label.Enabled = false;


                //Text Labels for sensor 2
                textBox_sensors_status_2.Visible = false;
                textBox_sensors_status_2.Enabled = false;
                textBox_sensor_location_2.Visible = false;
                textBox_sensor_location_2.Enabled = false;
                textBox_sensor_ID_2.Visible = false;
                textBox_sensor_ID_2.Enabled = false;


                #endregion 


                for (int i = 0; i < MAX_NUMBER_OF_SENSORS; i++)
                {
                    PrevFullPkg[i] = 0;
                    PrevPartialPkg[i] = 0;
                    PrevEmptyPkg[i] = 0;
                    LastPkgTime[i] = DateTime.Now;
                    ElapsedConnectionTime[i] = TimeSpan.Zero;
                }
            }


            private void SetupConnectionStatusLabels()
            {

               InitializeConnectionStatusLabels();

               
                for (int i = 0; i < wockets_controller._Receivers.Count; i++)
                {

                    switch (i)
                    {

                        case 0:
                            textBox_sensors_status_0.Visible = true;
                            textBox_sensors_status_0.Enabled = true;
                            textBox_sensor_location_0.Visible = true;
                            textBox_sensor_location_0.Enabled = true;
                            textBox_sensor_ID_0.Visible = true;
                            textBox_sensor_ID_0.Enabled = true;

                            textBox_spanel_sensors_location_0.Visible = true;
                            textBox_spanel_sensors_location_0.Enabled = true;
                            textBox_spanel_ac_full_0.Visible = true;
                            textBox_spanel_ac_full_0.Enabled = true;
                            textBox_spanel_ac_full_0_label.Visible = true;
                            textBox_spanel_ac_full_0_label.Enabled = true;
                            textBox_spanel_ac_last_0.Visible = true;
                            textBox_spanel_ac_last_0.Enabled = true;
                            textBox_spanel_ac_last_0_label.Visible = true;
                            textBox_spanel_ac_last_0_label.Enabled = true;
                            textBox_spanel_ac_new_0.Visible = true;
                            textBox_spanel_ac_new_0.Enabled = true;
                            textBox_spanel_ac_new_0_label.Visible = true;
                            textBox_spanel_ac_new_0_label.Enabled = true;
                            textBox_spanel_ac_partial_0.Visible = true;
                            textBox_spanel_ac_partial_0.Enabled = true;
                            textBox_spanel_ac_partial_0_label.Visible = true;
                            textBox_spanel_ac_partial_0_label.Enabled = true;
                            textBox_spanel_ac_empty_0.Visible = true;
                            textBox_spanel_ac_empty_0.Enabled = true;
                            textBox_spanel_ac_empty_0_label.Visible = true;
                            textBox_spanel_ac_empty_0_label.Enabled = true;
                            break;

                        case 1:
                            textBox_sensors_status_1.Visible = true;
                            textBox_sensors_status_1.Enabled = true;
                            textBox_sensor_location_1.Visible = true;
                            textBox_sensor_location_1.Enabled = true;
                            textBox_sensor_ID_1.Visible = true;
                            textBox_sensor_ID_1.Enabled = true;

                            textBox_spanel_sensors_location_1.Visible = true;
                            textBox_spanel_sensors_location_1.Enabled = true;
                            textBox_spanel_ac_full_1.Visible = true;
                            textBox_spanel_ac_full_1.Enabled = true;
                            textBox_spanel_ac_full_1_label.Visible = true;
                            textBox_spanel_ac_full_1_label.Enabled = true;
                            textBox_spanel_ac_last_1.Visible = true;
                            textBox_spanel_ac_last_1.Enabled = true;
                            textBox_spanel_ac_last_1_label.Visible = true;
                            textBox_spanel_ac_last_1_label.Enabled = true;
                            textBox_spanel_ac_new_1.Visible = true;
                            textBox_spanel_ac_new_1.Enabled = true;
                            textBox_spanel_ac_new_1_label.Visible = true;
                            textBox_spanel_ac_new_1_label.Enabled = true;
                            textBox_spanel_ac_partial_1.Visible = true;
                            textBox_spanel_ac_partial_1.Enabled = true;
                            textBox_spanel_ac_partial_1_label.Visible = true;
                            textBox_spanel_ac_partial_1_label.Enabled = true;
                            textBox_spanel_ac_empty_1.Visible = true;
                            textBox_spanel_ac_empty_1.Enabled = true;
                            textBox_spanel_ac_empty_1_label.Visible = true;
                            textBox_spanel_ac_empty_1_label.Enabled = true;
                            break;

                        case 2:
                            textBox_sensors_status_2.Visible = true;
                            textBox_sensors_status_2.Enabled = true;
                            textBox_sensor_location_2.Visible = true;
                            textBox_sensor_location_2.Enabled = true;
                            textBox_sensor_ID_2.Visible = true;
                            textBox_sensor_ID_2.Enabled = true;

                            break;

                        default:
                            break;
                    }
                }
               
           
            }


        #endregion


        #region Swap Sensors


        private void GoToSwapButton_Click(object sender, EventArgs e)
            {
                
                GoToSwapButton.Enabled = false;

                appLogger.Debug("Swapping Sensors Button Clicked");

                TurnOnPanel(PanelID.CONNECTION);


                try
                {
                    is_rebooting = true;

                    #region Save the app status to file

                    try
                    {
                        StreamWriter wr_status = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_appstatus.txt");
                        wr_status.WriteLine("swap");
                        wr_status.Close();
                    }
                    catch (Exception ex)
                    {
                        appLogger.Debug("CollectDataUser.cs: the app status -- swap-- failed to be written to file. Ex: " + ex);
                    }

                    #endregion


                    //TODO: monitor the time that takes to receive the disconnect response
                    //      to avoid the operation hangs.
                    #region commented
                    //Disconnect current sensors set from kernel
                    //WocketsDisconnect();
                    //UpdateMsg("Clossing Application");
                    //appLogger.Debug("Closing Application");
                    //Thread.Sleep(1000);
                    #endregion

                    //close application & reboot
                    this.Close();
                }
                catch (Exception ex)
                {
                    appLogger.Debug("An exception ocurred when trying to disconnect from kernel, after the swap button was clicked. Ex: " + ex.ToString());
                }
            }


        #region Swap Button commented
        //private void SwapSensorsButton_Click(object sender, EventArgs e)
        //{
        //    SwapSensorsButton.Enabled = false;
        //    appLogger.Debug("Swapping Sensors Button Clicked");

        //    TurnOnPanel(PanelID.CONNECTION);


        //    try
        //    {
        //        is_rebooting = true;

        //        #region Save the app status to file

        //        try
        //        {
        //            StreamWriter wr_status = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_appstatus.txt");
        //            wr_status.WriteLine("swap");
        //            wr_status.Close();
        //        }
        //        catch (Exception ex)
        //        {
        //            appLogger.Debug("CollectDataUser.cs: the app status -- swap-- failed to be written to file. Ex: " + ex);
        //        }

        //        #endregion


        //        //TODO: monitor the time that takes to receive the disconnect response
        //        //      to avoid the operation hangs.
        //        #region commented
        //        //Disconnect current sensors set from kernel
        //        //WocketsDisconnect();
        //        //UpdateMsg("Clossing Application");
        //        //appLogger.Debug("Closing Application");
        //        //Thread.Sleep(1000);
        //        #endregion

        //        //close application & reboot
        //        this.Close();
        //    }
        //    catch (Exception ex)
        //    {
        //        appLogger.Debug("An exception ocurred when trying to disconnect from kernel, after the swap button was clicked. Ex: " + ex.ToString());
        //    }
        //}

        #endregion 



        private void Show_Swap_Panel(String status, String set, WocketsController wc)
        {
            try
            {

                //GoToSwapButton.Enabled = false;
                

                #region update application status

                if (status.CompareTo("Connected") == 0)
                {
                    string msg = "Collecting Data";
                    //textBox_sensors_status.Text = msg;
                    //textBox_sensors_status.ForeColor = Color.Green;

                    //update the sensor status panel
                    textBox_spanel_sensors_status.Text = msg;
                    textBox_spanel_sensors_status.ForeColor = Color.Green;

                    //update fields in main app actions panel
                    textBox_main_sensor_status.Text = msg;
                    textBox_main_sensor_status.ForeColor = Color.Green;
                }
                else
                {
                    string msg = "Waiting For Data";
                    //textBox_sensors_status.Text = msg;
                    //textBox_sensors_status.ForeColor = Color.DimGray;

                    //update the sensor status panel
                    textBox_spanel_sensors_status.Text = msg;
                    textBox_spanel_sensors_status.ForeColor = Color.DimGray;

                    //update fields in main app actions panel
                    textBox_main_sensor_status.Text = msg;
                    textBox_main_sensor_status.ForeColor = Color.DimGray;
                }

                #endregion


                #region  update sensors set ID

                UpdateSensorSetIDColor(sensor_set);
                ResetStatusLabels();

                if (sensor_set.CompareTo("red") == 0)
                {
                    //textBox_sensor_set_ID.Text = "RED SET";
                    //textBox_sensor_set_ID.BackColor = Color.Tomato;
                    
                    //update sensors status panel
                    textBox_spanel_sensors_ID.Text = "RED SET";
                    textBox_spanel_sensors_ID.BackColor = Color.Tomato;

                    //update fields in main app actions panel
                    textBox_main_sensor_set_ID.Text = "RED SET";
                    textBox_main_sensor_set_ID.BackColor = Color.Tomato;
                }
                else
                {
                    //textBox_sensor_set_ID.Text = "GREEN SET";
                    //textBox_sensor_set_ID.BackColor = Color.YellowGreen;

                    //update sensors status panel
                    textBox_spanel_sensors_ID.Text = "GREEN SET";
                    textBox_spanel_sensors_ID.BackColor = Color.YellowGreen;

                    //update fields in main app actions panel
                    textBox_main_sensor_set_ID.Text = "GREEN SET";
                    textBox_main_sensor_set_ID.BackColor = Color.YellowGreen;
                }

                #endregion


                #region update sensors MACS & LOCATIONS on panel

                if (wc != null)
                {
                    for (int i = 0; i < wc._Receivers.Count; i++)
                    {
                        string slocation = "";

                        if (wc._Sensors[i]._Location != null)
                            slocation = wc._Sensors[i]._Location;

                        #region commented
                        //if( wc._Sensors[i]._Location.Contains("Right") )
                            //   slocation = "R. " + wc._Sensors[i]._Location.Substring("Right ".Length);
                            //else if (wc._Sensors[i]._Location.Contains("Left"))
                            //   slocation = "L. " + wc._Sensors[i]._Location.Substring("Left ".Length);
                        #endregion 


                        switch (i)
                        {
                            case 0:
                                textBox_sensor_ID_0.Text = "W";
                                textBox_sensor_location_0.Text = slocation;
                                textBox_spanel_sensors_location_0.Text = "W: " + ((RFCOMMReceiver)wc._Receivers[i])._Address.Substring(7) +" : " + slocation;
                                break;
                            case 1:
                                textBox_sensor_ID_1.Text = "A";
                                textBox_sensor_location_1.Text = slocation;
                                textBox_spanel_sensors_location_1.Text = "A: " + ((RFCOMMReceiver)wc._Receivers[i])._Address.Substring(7) +" : " + slocation;
                                break;
                            case 2:
                                textBox_sensor_ID_2.Text = "P";
                                textBox_sensor_location_2.Text = ((RFCOMMReceiver)wc._Receivers[i])._Address.Substring(7) +": " + slocation;
                                break;
                            default:
                                break;
                        }
                    }
                }

                #endregion


            }
            catch 
            {
                appLogger.Debug("Problem Reading Xml Parameters for Sensor Locations");
            }
        }

        
        private void UpdateSensorSetIDColor(string sensor_set_id)
        { 
            Color scolor = Color.Tomato;

            if (sensor_set_id.CompareTo("red") != 0)
                scolor = Color.YellowGreen;

            textBox_sensor_ID_0.BackColor = scolor;
            textBox_sensor_ID_1.BackColor = scolor;
            textBox_sensor_ID_2.BackColor = scolor;

        }


        private void ResetStatusLabels()
        {
            textBox_sensors_status_0.Text = "---";
            textBox_sensors_status_1.Text = "---";
            textBox_sensors_status_2.Text = "---";
        }


        private bool LoadSensorsFromMasterList(string[] loaded_sensor_data, string sensor_set_id, Dictionary<int, string> selected_locations)
        {
            bool success = false;
            
            try
            {
                // Open the Xml File containing the sensor parameters for Set 1
                if (LoadSensorSetFromXml(sensor_set_id))
                {
                    if (!CompareSensorSetToMasterList(sensor_set_id, loaded_sensor_data))
                        appLogger.Debug("CollectDataUser: the sensors data could NOT be compared with the Master List, an error ocurred and the function returned false.");


                    if (selected_locations == null)
                        selected_locations = new Dictionary<int, string>();

                    if (selected_locations.Count > 0)
                    {
                        for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
                        {
                            if (i < selected_sensor_locations.Count)
                                CurrentWockets._Controller._Sensors[i]._Location = selected_sensor_locations[i];
                            else
                                CurrentWockets._Controller._Sensors[i]._Location = "null";
                        }
                    }
                    else
                    {
                        for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
                        {
                            if (CurrentWockets._Controller._Sensors[i]._Location.CompareTo("null") != 0)
                                selected_locations.Add(i, CurrentWockets._Controller._Sensors[i]._Location);
                        }
                    }

                    success = true;
                }
                else
                   appLogger.Debug("CollectDataUser: sensors info could not be loaded from sensordata file. Loadsensors from MasterList function.");
                

            }
            catch
            {
                appLogger.Debug("CollectDataUser: an exeption occurred whre trying to load sensors from the Master List. Problem when assigning sensors locations.");
            }



            #region commented for now
            //if (loaded_sensor_data != null )
            //{
                #region Determine the sensor set to be loaded & load it to the wockets receivers (commented for now)

            //    //if (sensor_set_id.CompareTo(loaded_sensor_data[(int)MasterListParam.Set1_ID]) == 0)
            //    //{
            //    //    //Load Sensor Set 1   
                    
            //    //    #region commented for now
            //    //        //try
            //    //        //{
            //    //        //    if (File.Exists(Settings._MainWocketsDirectory + "\\updater_SensorData1.xml"))
            //    //        //        wc.FromXML(Settings._MainWocketsDirectory + "\\updater_SensorData1.xml");
            //    //        //    else
            //    //        //        wc.FromXML(Settings._MainWocketsDirectory + "\\SensorData1.xml");

            //    //        //    success = true;
            //    //        //}
            //    //        //catch
            //    //        //{
            //    //        //    appLogger.Debug("The SensorData1.Xml couldn't be opened.");
            //    //        //}
            //    //    #endregion

            //    //    // Open the Xml File containing the sensor parameters for Set 1
            //    //    //if (LoadSensorSetFromXml("red"))
            //    //    //{

            //    //        #region commented for now
            //    //        //#region If the sensors are different from the ones in the master list, update the wockets controller settings

            //    //        //try
            //    //        //{
            //    //        //    bool is_mac_changed = false;
            //    //        //    int mac_offset = ((int)MasterListParam.Set1_ID) + 2;

            //    //        //    for (int i = 0; i < wc._Receivers.Count; i++)
            //    //        //    {
            //    //        //        if ((((RFCOMMReceiver)wc._Receivers[i])._Address.CompareTo(loaded_sensor_data[mac_offset + i]) != 0) &
            //    //        //               (loaded_sensor_data[mac_offset + i].CompareTo("0") != 0))
            //    //        //        {
            //    //        //            //replace the mac address 
            //    //        //            ((RFCOMMReceiver)wc._Receivers[i])._Address = loaded_sensor_data[mac_offset + i];
            //    //        //            is_mac_changed = true;

            //    //        //            //TODO: send commands to get the sensor calibration values & effective sampling rate
            //    //        //        }
            //    //        //    }


            //    //        //    //if macs are different, save the new sensor parameters to the Xml file
            //    //        //    if (is_mac_changed)
            //    //        //    {
            //    //        //        StreamWriter sensors_data_xml = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_SensorData1.xml");
            //    //        //        sensors_data_xml.Write(wc.ToXML());
            //    //        //        sensors_data_xml.Close();
            //    //        //    }
            //    //        //}
            //    //        //catch (Exception e)
            //    //        //{
            //    //        //    success = false;
            //    //        //    appLogger.Debug("An exeption occurred when trying to update macs from master list, set1. Ex: " + e.ToString());
            //    //        //}

            //    //        //#endregion
            //    //        #endregion 

            //    //        //if( CompareSensorSetToMasterList(wc,"red", out is_mac_changed) )
            //    //        //  success = true;
            //    //   // }

                    
            //    //}
            //    //else
            //    //{
            //    //    #region Load SensorSet 2 (commented for now)

            //    //        ////Open the Xml File containing the sensor parameters for Set 2
            //    //        //try
            //    //        //{
            //    //        //    if (File.Exists( Settings._MainWocketsDirectory + "\\updater_SensorData2.xml"))
            //    //        //        wc.FromXML(Settings._MainWocketsDirectory   + "\\updater_SensorData2.xml");
            //    //        //    else
            //    //        //        wc.FromXML(Settings._MainWocketsDirectory + "\\SensorData2.xml");

            //    //        //    success = true;
            //    //        //}
            //    //        //catch
            //    //        //{ appLogger.Debug("The SensorData2.Xml couldn't be opened."); }


            //    //        //#region If the sensors are different from the ones in the master list, update the controller settings

            //    //        //try
            //    //        //{
            //    //        //    bool is_mac_changed = false;
            //    //        //    int mac_offset = ((int)MasterListParam.Set2_ID) + 2;


            //    //        //    for (int i = 0; i < wc._Receivers.Count; i++)
            //    //        //    {
            //    //        //        if (  (((RFCOMMReceiver)wc._Receivers[i])._Address.CompareTo(loaded_sensor_data[mac_offset + i]) != 0) &
            //    //        //              (loaded_sensor_data[mac_offset + i].CompareTo("0") != 0) )
            //    //        //        {
            //    //        //            //replace the mac address 
            //    //        //            ((RFCOMMReceiver)wc._Receivers[i])._Address = loaded_sensor_data[mac_offset + i];
            //    //        //            is_mac_changed = true;

            //    //        //            //TODO: send commands to get the sensor calibration values & effective sampling rate
            //    //        //        }
            //    //        //    }


            //    //        //    //Save the new sensor parameters to the Xml file
            //    //        //    if (is_mac_changed)
            //    //        //    {
            //    //        //       StreamWriter sensors_data_xml = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_SensorData2.xml");
            //    //        //            sensors_data_xml.Write(wc.ToXML());
            //    //        //            sensors_data_xml.Close();
            //    //        //    }

            //    //        //}
            //    //        //catch(Exception e)
            //    //        //{
            //    //        //    success = false;
            //    //        //    appLogger.Debug("An exeption occurred when trying to update macs with master list, set2. Ex: " + e.ToString()); 
            //    //        //}

            //    //        //#endregion

            //    //    #endregion
                    


            //    //}

            //    ////Load flag that specifies if data needs to be uploaded to the server automatically
            //    //if (sensor_data[(int)MasterListParam.UploadRawData].ToLower().CompareTo("no") == 0)
            //    //    upload_raw_data = false;

            //    #endregion 
            //}
            //else
            //{
            //    #region Load Sensor data directly from Default Xml files (commented for now)

            //        //if (sensor_set_id.CompareTo("red") == 0)
            //        //{
            //        //    #region Open the Xml File containing the sensor parameters for Set 1

            //        //    try
            //        //    {
            //        //        if (File.Exists(Settings._MainWocketsDirectory + "\\updater_SensorData1.xml"))
            //        //            wc.FromXML(Settings._MainWocketsDirectory + "\\updater_SensorData1.xml");
            //        //        else 
            //        //            wc.FromXML(Settings._MainWocketsDirectory + "\\SensorData1.xml");
                            
            //        //        success = true;

            //        //    }
            //        //    catch
            //        //    {
            //        //        success = false;
            //        //        //TODO: Notify the user/researcher in this case
            //        //        appLogger.Debug("The SensorData1.Xml couldn't be opened.");
            //        //    }

            //        //    #endregion

            //        //}
            //        //else
            //        //{
            //        //    #region Open the Xml File containing the sensor parameters for Set 2

            //        //        try
            //        //        {
            //        //            if (File.Exists(Settings._MainWocketsDirectory + "\\updater_SensorData2.xml"))
            //        //                wc.FromXML(Settings._MainWocketsDirectory + "\\updater_SensorData2.xml");
            //        //            else
            //        //                wc.FromXML(Settings._MainWocketsDirectory + "\\SensorData2.xml");
                               
            //        //            success = true;
            //        //        }
            //        //        catch
            //        //        {
            //        //            success = false;
            //        //            //TODO: Notify the user/researcher in this case
            //        //            appLogger.Debug("The SensorData2.Xml couldn't be opened.");
            //        //        }

            //        //    #endregion
            //        //}

                #endregion 
            //}
            #endregion 


            //TODO: notify user/researcher if MACs are valid.
            return success;
        }



        private bool UpdateSensorLocations(Dictionary<int, string> selected_locations)
        {
            bool is_updated = false;

            try
            {
                if( selected_locations != null )
                {                
                    if( CurrentWockets._Controller != null )
                        if( CurrentWockets._Controller._Sensors != null )
                          for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
                           {
                                if (i < selected_sensor_locations.Count)
                                    CurrentWockets._Controller._Sensors[i]._Location = selected_sensor_locations[i];
                                else
                                    CurrentWockets._Controller._Sensors[i]._Location = "null";
                           }

                    is_updated = true;
                }
                else
                    appLogger.Debug("CollectDataUser: UpdateSensorsLocations: selected_locations = null");
            }
            catch
            {
                appLogger.Debug("CollectDataUser: an exeption occurred when trying to update the sensor locations in controller: UpdateSensorLocations()");
            }

            return is_updated;
        }


        private bool LoadSensorSetFromXml(string sensor_set_ID)
        {
            bool success = false;
            string xml_filename = "";
            
            //Open the Xml File containing the sensor parameters for the Set
            try
            {
                if (sensor_set_ID.CompareTo("red") == 0)
                {
                    if (File.Exists(Settings._MainWocketsDirectory + "\\updater_SensorData1.xml"))
                        xml_filename = "\\updater_SensorData1.xml";
                    else
                        if (File.Exists(Settings._MainWocketsDirectory + "\\SensorData1.xml"))
                            xml_filename = "\\SensorData1.xml";
                }
                else
                {
                    if (File.Exists(Settings._MainWocketsDirectory + "\\updater_SensorData2.xml"))
                        xml_filename = "\\updater_SensorData2.xml";
                    else
                        if (File.Exists(Settings._MainWocketsDirectory + "\\SensorData2.xml"))
                            xml_filename = "\\SensorData2.xml";
                }



                if (xml_filename.CompareTo("") != 0)
                {
                    CurrentWockets._Controller.FromXML(Settings._MainWocketsDirectory + xml_filename);

                    if (CurrentWockets._Controller != null)
                    {
                        if (CurrentWockets._Controller._Receivers != null & CurrentWockets._Controller._Sensors != null)
                            if (CurrentWockets._Controller._Receivers.Count > 0 & CurrentWockets._Controller._Sensors.Count > 0)
                                success = true;
                            else
                                appLogger.Debug("An error occurred when trying to read the " + xml_filename + ", wc._Receivers.Count = 0");
                        else
                            appLogger.Debug("An error occurred when trying to read the " + xml_filename + ", wc._Receivers = null");
                    }
                    else
                        appLogger.Debug("An error occurred when trying to read the " + xml_filename + ", wc = null");
                }
                else
                {
                    appLogger.Debug("An error occurred when trying to read the " + xml_filename + ". The file was not found.");
                }
                
            }
            catch
            {
                appLogger.Debug("The " + xml_filename + " for " + sensor_set_ID + " couldn't be opened."); 
            }
            

           return success;
        }


        private bool CompareSensorSetToMasterList(string sensor_set_ID, string[] loaded_sensor_data)
        {
            bool success = false;
            int mac_offset = 0;
            
            
            try
            {
                if (CurrentWockets._Controller != null)
                {
                    if (CurrentWockets._Controller._Receivers != null)
                    {
                        if (CurrentWockets._Controller._Receivers.Count > 0)
                        {
                            if (sensor_set_ID.CompareTo("red") == 0)
                               mac_offset = ((int)MasterListParam.Set1_ID) + 2;
                            else
                               mac_offset = ((int)MasterListParam.Set2_ID) + 2;
                                

                            for (int i = 0; i < CurrentWockets._Controller._Receivers.Count; i++)
                            {
                                if ((((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address.CompareTo(loaded_sensor_data[mac_offset + i]) != 0) &
                                       (loaded_sensor_data[mac_offset + i].CompareTo("0") != 0))
                                {
                                    //replace the mac address 
                                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address = loaded_sensor_data[mac_offset + i];
                                    
                                    //TODO: send commands to get the sensor calibration values & effective sampling rate
                                }
                            }

                          
                            try
                            {
                                //Load flag that specifies if data needs to be uploaded to the server automatically
                                if (loaded_sensor_data[(int)MasterListParam.UploadRawData].ToLower().CompareTo("no") == 0)
                                    upload_raw_data = false;
                            }
                            catch
                            {
                                appLogger.Debug("Problem reading the upload_raw_data variable from master list");  
                            }

                            success = true;
                        }
                        else
                            appLogger.Debug("An error occurred when trying to update macs from master list, wc._Receivers.Count = 0");  
                    }
                    else
                        appLogger.Debug("An error occurred when trying to update macs from master list, wc._Receivers = null");  
                }
                else
                    appLogger.Debug("An error occurred when trying to update macs from master list, wc = null");  
            }
            catch (Exception e)
            {
                appLogger.Debug("An exeption occurred when trying to update macs from master list, sensor set: " + sensor_set_ID + " Macs Changed = " + ". Ex: " + e.ToString());
            }


            return success;
        }


        private bool SaveSensorDataToXml(string sensor_set_ID)
        {
            bool success = false;

            //Save selected locations to local xml file
            string xml_filename = "";

            try
            {
                if (sensor_set_ID.CompareTo("red") == 0)
                    xml_filename = "\\updater_SensorData1.xml";
                else
                    xml_filename = "\\updater_SensorData2.xml";

                if (CurrentWockets._Controller != null)
                {
                    StreamWriter sensors_data_xml = new StreamWriter(Settings._MainWocketsDirectory + xml_filename);
                    sensors_data_xml.Write(CurrentWockets._Controller.ToXML());
                    sensors_data_xml.Close();

                    success = true;
                }
            }
            catch (Exception ex)
            {
                appLogger.Debug("program.cs: Exception when trying to save sensor data to the " + xml_filename + ". SetID: " + sensor_set + ". EX:" + ex.ToString());
            }


            return success;
        }


        private bool ChangeSensorSetID()
        {
            bool success = false;
            string setid = sensor_set;

            try
            {
                if (sensor_set.CompareTo("red") == 0)
                    setid = "green";
                else
                    setid = "red";

                StreamWriter wr_sensors = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_last_set.txt");
                wr_sensors.WriteLine(setid);
                wr_sensors.Flush();
                wr_sensors.Close();

                sensor_set = setid;

                success = true;
            }
            catch (Exception ex)
            {
                appLogger.Debug("An exception occurred when trying to save the set ID to file when it is changed." + ex.ToString());
            }

            return success;
        }


     #endregion 


        #region Connect/Disconnect Sensors Functions

        WocketsConfiguration wockets_controller_configuration;


        private bool InitializeWocketsController()
        {
            bool success = false;

            try
            {

                if (wockets_controller != null)
                {
                    wockets_controller.Dispose();
                    wockets_controller = null;
                }


                // Create the session directory
                //DateTime now = DateTime.Now;
                //Settings._DataStorageDirectory = Settings._MemoryCardDirectory + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");
                //if (!Directory.Exists(Settings._DataStorageDirectory))
                //    Directory.CreateDirectory(Settings._DataStorageDirectory);

                //TODO: separate the controller logger from the application one
                //Logger.InitLogger(Settings._DataStorageDirectory + "\\log\\");
                //appLogger.Debug("Session and log directories created.");


                wockets_controller = new WocketsController("", "", "");
                wockets_controller._StorageDirectory = Settings._DataStorageDirectory;
                CurrentWockets._Controller = wockets_controller;
                sensors_loaded = false;

                appLogger.Debug("Wockets controller initialized.");

                success = true;
            }
            catch (Exception e)
            {
                appLogger.Debug("Exception when trying to create the initialize the wockets controller. Ex: " + e.ToString());
            }

            return success;
        }



        private bool ConnetToWocketsController(string sensor_set_ID)
        {
            bool sucess = false;
           
            TurnOnPanel(PanelID.CONNECTION);
            label_kernel_status.Text = "Connecting To Wockets";
            Application.DoEvents();
            Thread.Sleep(1000);


            if (sensors_loaded)
            {
                SaveSensorDataToXml(sensor_set_ID);


                #region Try to connect sensors to the wockets controller


                if (CurrentWockets._Controller._Sensors.Count > 0 )
                {

                    #region Load The Configuration Xml File

                    //Load the wockets configuration directory
                    wockets_controller_configuration = new WocketsConfiguration();
                    wockets_controller_configuration.FromXML(Settings._MainWocketsDirectory + "NeededFiles\\Master\\Configuration.xml");

                    try
                    {
                        File.Copy(Settings._MainWocketsDirectory + "NeededFiles\\Master\\Configuration.xml", CurrentWockets._Controller._StorageDirectory + "\\Configuration.xml");
                    }
                    catch (Exception e)
                    {
                        appLogger.Debug("program.cs: Exception when trying to copy the Configuration.xml file to storage card. " + e.ToString());
                    }


                    CurrentWockets._Configuration = wockets_controller_configuration;

                    #endregion


                    //Set memory mode to local
                    CurrentWockets._Controller._Mode = MemoryMode.BluetoothToLocal;

                    //Initialize wockets controller and set it to "bursty mode"
                    CurrentWockets._Controller._TMode = TransmissionMode.Bursty60;


                    //Initialize pointers to loaded sensors
                    for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                    {

                        if (CurrentWockets._Controller._Sensors[i]._Location.CompareTo("null") == 0)
                        {
                            appLogger.Debug("Program.cs: Sensor " + CurrentWockets._Controller._Sensors[i]._Address + "unloaded from xml template controller.");

                            CurrentWockets._Controller._Sensors.RemoveAt(i);
                            CurrentWockets._Controller._Receivers.RemoveAt(i);
                            CurrentWockets._Controller._Decoders.RemoveAt(i);
                        }
                        else
                        {
                            CurrentWockets._Controller._Receivers[i]._ID = i;
                            CurrentWockets._Controller._Decoders[i]._ID  = i;
                            CurrentWockets._Controller._Sensors[i]._ID   = i;
                            CurrentWockets._Controller._Sensors[i]._Receiver = CurrentWockets._Controller._Receivers[i];
                            CurrentWockets._Controller._Sensors[i]._Address  = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address;
                            CurrentWockets._Controller._Sensors[i]._Decoder  = CurrentWockets._Controller._Decoders[i];
                            CurrentWockets._Controller._Sensors[i]._Loaded   = true;
                            CurrentWockets._Controller._Sensors[i]._RootStorageDirectory = CurrentWockets._Controller._StorageDirectory + "\\data\\raw\\PLFormat\\";

                            appLogger.Debug("Program.cs: Sensor Loaded= " + CurrentWockets._Controller._Sensors[i]._Address);
                        }

                    }



                    #region Save the SensorData.Xml to the session data directory

                    try
                    {
                        StreamWriter sensors_data_xml = new StreamWriter(CurrentWockets._Controller._StorageDirectory + "\\SensorData.xml");
                        sensors_data_xml.Write(CurrentWockets._Controller.ToXML());
                        sensors_data_xml.Close();
                    }
                    catch (Exception e)
                    {
                        appLogger.Debug("program.cs: Exception when trying to copy the SensorData.xml file to storage card." + e.ToString());
                    }


                    #endregion


                    #region  Code Commented

                    #region commented
                    #region commented
                    ////Load sensors addresses to array list
                    //sensors_list = new ArrayList();
                    //for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                    //{
                    //    sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);
                    //    appLogger.Debug("Sensor Info Loaded From Xml, Sensor Set: " + sensor_set + "," +
                    //                 "MAC " + i.ToString() + ":"+ sensors_list[i]);
                    //}
                    #endregion

                    #region Suscribe to Kernel Events (commented)


                    //SuscribeToKernelEvents();

                    #endregion
                    #endregion


                    #region Initialize thread that tracks the connection status (commented)


                    //ACsUpdateTimer = new System.Windows.Forms.Timer();
                    //ACsUpdateTimer.Interval = 10000; //update every 10sec
                    //ACsUpdateTimer.Tick += new EventHandler(ACsUpdateTimer_Tick);
                    //ACsUpdateTimer.Enabled = false;
                    #endregion


                    #region Initialization of Connection Status Variables (commented)

                    #region commneted
                    //PrevFullPkg = new int[wockets_controller._Receivers.Count];
                    //PrevPartialPkg = new int[wockets_controller._Receivers.Count];
                    //PrevEmptyPkg = new int[wockets_controller._Receivers.Count];
                    //LastPkgTime = new DateTime[wockets_controller._Receivers.Count];
                    //ElapsedConnectionTime = new TimeSpan[wockets_controller._Receivers.Count];


                    //#region Initialize the sensor packets status text labels

                    //textBox_sensors_status_0.Visible = false;
                    //textBox_sensors_status_0.Enabled = false;
                    //textBox_sensor_location_0.Visible = false;
                    //textBox_sensor_location_0.Enabled = false;

                    //textBox_spanel_sensors_location_0.Visible = false;
                    //textBox_spanel_sensors_location_0.Enabled = false;
                    //textBox_spanel_ac_full_0.Visible = false;
                    //textBox_spanel_ac_full_0.Enabled = false;
                    //textBox_spanel_ac_full_0_label.Visible = false;
                    //textBox_spanel_ac_full_0_label.Enabled = false;
                    //textBox_spanel_ac_last_0.Visible = false;
                    //textBox_spanel_ac_last_0.Enabled = false;
                    //textBox_spanel_ac_last_0_label.Visible = false;
                    //textBox_spanel_ac_last_0_label.Enabled = false;
                    //textBox_spanel_ac_new_0.Visible = false;
                    //textBox_spanel_ac_new_0.Enabled = false;
                    //textBox_spanel_ac_new_0_label.Visible = false;
                    //textBox_spanel_ac_new_0_label.Enabled = false;
                    //textBox_spanel_ac_partial_0.Visible = false;
                    //textBox_spanel_ac_partial_0.Enabled = false;
                    //textBox_spanel_ac_partial_0_label.Visible = false;
                    //textBox_spanel_ac_partial_0_label.Enabled = false;
                    //textBox_spanel_ac_empty_0.Visible = false;
                    //textBox_spanel_ac_empty_0.Enabled = false;
                    //textBox_spanel_ac_empty_0_label.Visible = false;
                    //textBox_spanel_ac_empty_0_label.Enabled = false;




                    //textBox_sensors_status_1.Visible = false;
                    //textBox_sensors_status_1.Enabled = false;
                    //textBox_sensor_location_1.Visible = false;
                    //textBox_sensor_location_1.Enabled = false;


                    //textBox_spanel_sensors_location_1.Visible = false;
                    //textBox_spanel_sensors_location_1.Enabled = false;
                    //textBox_spanel_ac_full_1.Visible = false;
                    //textBox_spanel_ac_full_1.Enabled = false;
                    //textBox_spanel_ac_full_1_label.Visible = false;
                    //textBox_spanel_ac_full_1_label.Enabled = false;
                    //textBox_spanel_ac_last_1.Visible = false;
                    //textBox_spanel_ac_last_1.Enabled = false;
                    //textBox_spanel_ac_last_1_label.Visible = false;
                    //textBox_spanel_ac_last_1_label.Enabled = false;
                    //textBox_spanel_ac_new_1.Visible = false;
                    //textBox_spanel_ac_new_1.Enabled = false;
                    //textBox_spanel_ac_new_1_label.Visible = false;
                    //textBox_spanel_ac_new_1_label.Enabled = false;
                    //textBox_spanel_ac_partial_1.Visible = false;
                    //textBox_spanel_ac_partial_1.Enabled = false;
                    //textBox_spanel_ac_partial_1_label.Visible = false;
                    //textBox_spanel_ac_partial_1_label.Enabled = false;
                    //textBox_spanel_ac_empty_1.Visible = false;
                    //textBox_spanel_ac_empty_1.Enabled = false;
                    //textBox_spanel_ac_empty_1_label.Visible = false;
                    //textBox_spanel_ac_empty_1_label.Enabled = false;


                    //textBox_sensors_status_2.Visible = false;
                    //textBox_sensors_status_2.Enabled = false;
                    //textBox_sensor_location_2.Visible = false;
                    //textBox_sensor_location_2.Enabled = false;



                    //for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                    //{

                    //    #region commented
                    //    //PrevFullPkg[np] = 0;
                    //    //PrevPartialPkg[np] = 0;
                    //    //PrevEmptyPkg[np] = 0;
                    //    //LastPkgTime[np] = DateTime.Now;
                    //    //ElapsedConnectionTime[np] = TimeSpan.Zero;
                    //    #endregion 


                    //    switch (np)
                    //    {

                    //        case 0:
                    //            textBox_sensors_status_0.Visible = true;
                    //            textBox_sensors_status_0.Enabled = true;
                    //            textBox_sensor_location_0.Visible = true;
                    //            textBox_sensor_location_0.Enabled = true;

                    //            textBox_spanel_sensors_location_0.Visible = true;
                    //            textBox_spanel_sensors_location_0.Enabled = true;
                    //            textBox_spanel_ac_full_0.Visible = true;
                    //            textBox_spanel_ac_full_0.Enabled = true;
                    //            textBox_spanel_ac_full_0_label.Visible = true;
                    //            textBox_spanel_ac_full_0_label.Enabled = true;
                    //            textBox_spanel_ac_last_0.Visible = true;
                    //            textBox_spanel_ac_last_0.Enabled = true;
                    //            textBox_spanel_ac_last_0_label.Visible = true;
                    //            textBox_spanel_ac_last_0_label.Enabled = true;
                    //            textBox_spanel_ac_new_0.Visible = true;
                    //            textBox_spanel_ac_new_0.Enabled = true;
                    //            textBox_spanel_ac_new_0_label.Visible = true;
                    //            textBox_spanel_ac_new_0_label.Enabled = true;
                    //            textBox_spanel_ac_partial_0.Visible = true;
                    //            textBox_spanel_ac_partial_0.Enabled = true;
                    //            textBox_spanel_ac_partial_0_label.Visible = true;
                    //            textBox_spanel_ac_partial_0_label.Enabled = true;
                    //            textBox_spanel_ac_empty_0.Visible = true;
                    //            textBox_spanel_ac_empty_0.Enabled = true;
                    //            textBox_spanel_ac_empty_0_label.Visible = true;
                    //            textBox_spanel_ac_empty_0_label.Enabled = true;

                    //            break;
                    //        case 1:
                    //            textBox_sensors_status_1.Visible = true;
                    //            textBox_sensors_status_1.Enabled = true;
                    //            textBox_sensor_location_1.Visible = true;
                    //            textBox_sensor_location_1.Enabled = true;

                    //            textBox_spanel_sensors_location_1.Visible = true;
                    //            textBox_spanel_sensors_location_1.Enabled = true;
                    //            textBox_spanel_ac_full_1.Visible = true;
                    //            textBox_spanel_ac_full_1.Enabled = true;
                    //            textBox_spanel_ac_full_1_label.Visible = true;
                    //            textBox_spanel_ac_full_1_label.Enabled = true;
                    //            textBox_spanel_ac_last_1.Visible = true;
                    //            textBox_spanel_ac_last_1.Enabled = true;
                    //            textBox_spanel_ac_last_1_label.Visible = true;
                    //            textBox_spanel_ac_last_1_label.Enabled = true;
                    //            textBox_spanel_ac_new_1.Visible = true;
                    //            textBox_spanel_ac_new_1.Enabled = true;
                    //            textBox_spanel_ac_new_1_label.Visible = true;
                    //            textBox_spanel_ac_new_1_label.Enabled = true;
                    //            textBox_spanel_ac_partial_1.Visible = true;
                    //            textBox_spanel_ac_partial_1.Enabled = true;
                    //            textBox_spanel_ac_partial_1_label.Visible = true;
                    //            textBox_spanel_ac_partial_1_label.Enabled = true;
                    //            textBox_spanel_ac_empty_1.Visible = true;
                    //            textBox_spanel_ac_empty_1.Enabled = true;
                    //            textBox_spanel_ac_empty_1_label.Visible = true;
                    //            textBox_spanel_ac_empty_1_label.Enabled = true;

                    //            break;
                    //        case 2:
                    //            textBox_sensors_status_2.Visible = true;
                    //            textBox_sensors_status_2.Enabled = true;
                    //            textBox_sensor_location_2.Visible = true;
                    //            textBox_sensor_location_2.Enabled = true;
                    //            break;
                    //        default:
                    //            break;
                    //    }
                    //}
                    //#endregion

                    #endregion

                    #endregion

                    #endregion


                    SetupConnectionStatusLabels();

                    //TODO: see if I can past this to the initialization segment
                    InitializeUploadStatusVariables();



                    #region Launch Wockets Controller for Data Collection


                    try
                    {
                        CurrentWockets._Controller.Initialize();
                        _WocketsRunning = true;
                        appLogger.Debug("Program.cs: The wockets controller successfully initialized.");

                        if (WocketsConnect(_WocketsRunning))
                        {

                            label_kernel_status.Text = "Wockets Connected";
                            Application.DoEvents();
                            Thread.Sleep(1000);

                            LaunchWocketsQuestionarie();

                            SaveApplicationStatusToFile("running");


                            #region Save the app status to file (commented)

                            //try
                            //{
                            //    StreamWriter wr_status = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_appstatus.txt");
                            //    wr_status.WriteLine("running");
                            //    wr_status.Close();
                            //}
                            //catch (Exception ex)
                            //{
                            //    appLogger.Debug("CollectDataUser.cs: The wockets controller successfully initialized, but the app status -- running-- failed to be written to file. Ex: " + ex);
                            //}

                            #endregion


                            sucess = true;
                        }
                        else
                        {
                            //TODO: consolidate this part
                            //TurnOnPanel(PanelID.CONNECTION);
                            label_kernel_status.Text = "The wockets cannot connect. Please restart the Application.";
                            Application.DoEvents();

                            Thread.Sleep(2000);

                            Application.Exit();
                            System.Diagnostics.Process.GetCurrentProcess().Kill();
                        }

                    }
                    catch (Exception e)
                    {
                        appLogger.Debug("Program.cs: The wockets controller was NOT initialized. Ex:" + e.ToString());

                        //TurnOnPanel(PanelID.CONNECTION);
                        label_kernel_status.Text = "The wockets controller was NOT initialized. Please restart the Application.";
                        Application.DoEvents();

                        Thread.Sleep(2000);

                        Application.Exit();
                        System.Diagnostics.Process.GetCurrentProcess().Kill();
                    }


                    #endregion

                }
                else //Sensors Macs not loaded
                {
                    #region send error message and quit app

                    appLogger.Debug("The Sensors Couldn't be loaded. Please restart the Application.");

                    //TurnOnPanel(PanelID.CONNECTION);
                    label_kernel_status.Text = "The sensors couldn't be loaded. Please restart the application.";
                    Application.DoEvents();
                    Thread.Sleep(2000);

                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();

                    #endregion

                }

                #endregion If there are sensors, connect the wockets controller


            }
            else
            {
                //TurnOnPanel(PanelID.CONNECTION);
                label_kernel_status.Text = "Wockets Not Loaded";
                Application.DoEvents();
                Thread.Sleep(1000);
                appLogger.Debug("program.cs: Sensors were not loaded correctly. LoadSensors Function returned false.");
            }

            return sucess;
        }



        private bool WocketsConnect(bool wockets_running)
        {
            bool success = false;

            if (wockets_running)
            {
                try
                {
                    appLogger.Debug("Wockets Connected");
                    UpdateMsg("Wockets Connected");

                    //updates the sensor set used by kernel (commented)
                    //(not necessary, this should be in the app innitialization and swap code)
                    #region commented
                    //try
                    //{
                    //    appLogger.Debug("saving the current set ID to file");
                    //    StreamWriter wr_sensors = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_last_set.txt");
                    //    wr_sensors.WriteLine(sensor_set);
                    //    wr_sensors.Flush();
                    //    wr_sensors.Close();
                    //}
                    //catch (Exception e)
                    //{
                    //    appLogger.Debug("An exception occurred when trying to save set status to file, after receiving kernel connected response. Ex: " + e.ToString());
                    //}
                    #endregion


                    //Initialize the connection status counters and elapsed time variables
                    for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                    {
                        PrevFullPkg[np] = 0;
                        PrevPartialPkg[np] = 0;
                        PrevEmptyPkg[np] = 0;
                        LastPkgTime[np] = DateTime.Now;
                        ElapsedConnectionTime[np] = TimeSpan.Zero;
                    }


                    //Update the sensors status variable on the swap panel screen
                    Show_Swap_Panel("Connected", sensor_set, wockets_controller);
                    TurnOnPanel(PanelID.SWAP);

                    //Update the main application menu options
                    //menuMainAppActions.Text = "Minimize";

                    //Start the connection status thread 
                    if (!ACsUpdateTimer.Enabled)
                        StartACsUpdater();

                    success = true;

                }
                catch (Exception ex)
                {
                    appLogger.Debug("An exception occurred while executing the kernel connect sequence. Ex: " + ex.ToString());
                }

            }
            else
            {
                appLogger.Debug("program.cs: WocketsConnect(): Trying to connect, but _WocketsRunning variable = false.");
            }

            return success;

        }


        private void WocketsDisconnect()
        {

            if (_WocketsRunning)
            {
                try
                {

                    TurnOnPanel(PanelID.CONNECTION);
                    label_kernel_status.Text = "Disconnecting Wockets";
                    Application.DoEvents();
                    Thread.Sleep(500);

                    if (CurrentWockets._Controller != null)
                    {
                        
                        CurrentWockets._Controller.Dispose();
                        CurrentWockets._Controller = null;
                        _WocketsRunning = false;
                        SynchronizedLogger.Flush();
                    }

                    label_kernel_status.Text = "Wockets Disconnected";
                    Application.DoEvents();
                    Thread.Sleep(500);

                    appLogger.Debug("Wockets Disconnected");
      
                }
                catch (Exception e)
                {
                    appLogger.Debug("Exception when disconnecting sensors:" + e.ToString());
                }


                if ( is_rebooting )
                {
                    try
                    {
                        
                        //Determine which set will be used 
                        if (this.sensor_set.CompareTo("red") == 0)
                            sensor_set = "green";
                        else
                            sensor_set = "red";

                        //Indicate the swap sequence in the status files
                        StreamWriter wr_sensors = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_last_set.txt");

                        wr_sensors.WriteLine(sensor_set);
                        wr_sensors.Flush();
                        wr_sensors.Close();

                    }
                    catch (Exception ex)
                    {
                        appLogger.Debug("An exception occurred when trying to save set ID to file after disconnecting." + ex.ToString());
                    }
                }

            }
        }

        private bool SaveApplicationStatusToFile(string my_app_status)
        {
            bool success = false;

            try
            {
                StreamWriter wr_status = new StreamWriter(Settings._MainWocketsDirectory + "\\updater_appstatus.txt");
                wr_status.WriteLine(my_app_status);
                wr_status.Close();
                
                this.app_status = my_app_status;

                success = true;
            }
            catch (Exception ex)
            {
                appLogger.Debug("CollectDataUser.cs: The wockets controller successfully initialized, but the app status -- running-- failed to be written to file. Ex: " + ex);
            }

            return success;
        }


    #endregion


        #region Connection Status Message Callback 

        delegate void UpdateMsgCallback(string msg);

         private void UpdateMsg(string msg)
        {
            try
            {
            //     InvokeRequired required compares the thread ID of the
            //     calling thread to the thread ID of the creating thread.
            //     If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateMsgCallback d = new UpdateMsgCallback(UpdateMsg);
                    this.Invoke(d, new object[] { msg });
                }
                else
                {
                    label_kernel_status.Text = msg;
                    Application.DoEvents();
                }

            }
            catch (Exception e)
            {
                appLogger.Debug("Exception in the Update Msg function, kernel callback. Ex: " + e.ToString());
            }
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
            appLogger.Debug("Rebooting");
            ExitWindowsEx((uint)ExitWindowsAction.EWX_REBOOT, 0);
        }


        #region restart silently code commented
            //public enum SND_SOUNDTYPE
       // {
       //     On,
       //     File,
       //     Vibrate,
       //     None
       // }

       //private enum SND_EVENT
       // {
       //     All,
       //     RingLine1,
       //     RingLine2,
       //     KnownCallerLine1,
       //     RoamingLine1,
       //     RingVoip
       // }

       //[StructLayout(LayoutKind.Sequential)]
       //private struct SNDFILEINFO
       // {
       //     [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
       //     public string szPathName;
       //     [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
       //     public string szDisplayName;
       //     public SND_SOUNDTYPE sstType;
       // }

       //[DllImport("coredll.dll")]
       //public static extern void AudioUpdateFromRegistry();

       //[DllImport("aygshell.dll", SetLastError = true)]
       //private static extern uint SndSetSound(SND_EVENT seSoundEvent, ref SNDFILEINFO pSoundFileInfo, bool fSuppressUI);

       //[DllImport("aygshell.dll", SetLastError = true)]
       //private static extern uint SndGetSound(SND_EVENT seSoundEvent, ref SNDFILEINFO pSoundFileInfo);


       //static void SetProfileNormal(SND_EVENT mysnd)
       //{
       //    SNDFILEINFO soundFileInfo = new SNDFILEINFO();
       //    soundFileInfo.sstType = SND_SOUNDTYPE.On;
       //    uint num = SndSetSound(mysnd, ref soundFileInfo, true);
       //    AudioUpdateFromRegistry();

       //}

       //static void SetProfileVibrate()
       //{
       //    SNDFILEINFO soundFileInfo = new SNDFILEINFO();
       //    soundFileInfo.sstType = SND_SOUNDTYPE.Vibrate;
       //    uint num = SndSetSound(SND_EVENT.All, ref soundFileInfo, true);
       //    AudioUpdateFromRegistry();
       //}

       //static void SetProfileMuted()
       //{
       //    SNDFILEINFO soundFileInfo = new SNDFILEINFO();
       //    soundFileInfo.sstType = SND_SOUNDTYPE.None;
       //    uint num = SndSetSound(SND_EVENT.All, ref soundFileInfo, true);
       //    AudioUpdateFromRegistry();
       //}

       //private bool IsInVibrateMode()
       //{
       //    SNDFILEINFO info = new SNDFILEINFO();
       //    SndGetSound(SND_EVENT.All, ref info);
       //    return (info.sstType == SND_SOUNDTYPE.Vibrate);
       //}

       //private bool IsMuted()
       //{
       //    SNDFILEINFO info = new SNDFILEINFO();
       //    SndGetSound(SND_EVENT.All, ref info);
       //    return (info.sstType == SND_SOUNDTYPE.None);
       //}


       //public enum Volumes : int
       //{
       //    OFF = 0,

       //    LOW = 858993459,

       //    NORMAL = 1717986918,

       //    MEDIUM = -1717986919,

       //    HIGH = -858993460,

       //    VERY_HIGH = -1
       //}


       //[DllImport("coredll.dll", SetLastError = true)]
       // internal static extern int waveOutSetVolume(IntPtr device, int volume);

       //[DllImport("coredll.dll", SetLastError = true)]
       // internal static extern int waveOutGetVolume(IntPtr device, ref int volume);
        #endregion


     #endregion


        #region Exit/terminate application functions


        private void TerminateLogUploader()
        {
            try
            {
                System.Diagnostics.Process uploader_process = null;
                if (Is_LogUploader_Running(out uploader_process))
                {
                    if (uploader_process != null)
                    {
                        uploader_process.Kill();
                        Thread.Sleep(500);
                    }
                }
            }
            catch(Exception  e)
            { appLogger.Debug("An exception occurred when trying to terminate the log uploader. Ex: " + e.ToString()); }
        }


        private void TerminateDataUploader()
        {
            try
            {
                System.Diagnostics.Process uploader_process = null;
                if (Is_DataUploader_Running(out uploader_process))
                {
                    if (uploader_process != null)
                    {
                        uploader_process.Kill();
                        Thread.Sleep(500);
                    }
                }
            }
            catch(Exception e)
            { appLogger.Debug("An exception occurred when trying to terminate the data uploader. Ex: " + e.ToString()); }  
        }


        public void Disconnect_WocketsController()
        {
            try
            {
                appLogger.Debug("Starting to disconnect controller");
                is_rebooting = false;

                //Stop Update Upload Thread if running
                StopUpdateUploadThread();

                //Stop status monitoring thread
                StopACsUpdater();

                //Wait for the system to stabilize and check that threads have finished
                Thread.Sleep(1000);

                //Termine uploaders if running
                TerminateDataUploader();
                TerminateLogUploader();
                TerminateWocketsQuestionarie();

                //Terminate Data Collection
                WocketsDisconnect();

               
                appLogger.Debug("Wockets Disconnected");
                Thread.Sleep(1000);

            }
            catch (Exception e)
            { appLogger.Debug("An exception occurred when trying to disconnect wockets. Ex: " + e.ToString()); }

        }


        public void TerminateApp()
        {
            try
            {
                appLogger.Debug("Starting to quit application");

                //Stop Update Upload Thread if running
                StopUpdateUploadThread();

                //Stop status monitoring thread
                StopACsUpdater();

                //Wait for the system to stabilize and check that threads have finished
                Thread.Sleep(1000);

                //Termine uploaders if running
                TerminateDataUploader();
                TerminateLogUploader();
                TerminateWocketsQuestionarie();

                //Terminate the upload logger
                if (!UploadLoggerEvents.Dispose())
                    appLogger.Debug("Exception ocurred when the event upload logger was disposed.");
                
                //Terminate Data Collection
                WocketsDisconnect();

                //Close the hidden window 
                this.messageWindow.Dispose();

                UpdateMsg("Closing Application");
                appLogger.Debug("Closing Application");
                Thread.Sleep(1000);

            }
            catch(Exception e)
            { 
                appLogger.Debug("An exception occurred when trying to quit the application. Ex: " + e.ToString() ); 
            }
        }


        private void WocketsMainForm_Closing(object sender, CancelEventArgs e)
        {
            TerminateApp();   
        }
        

        private void WocketsMainForm_Closed(object sender, EventArgs e)
        {
                if (!is_rebooting)
                {
                    appLogger.Debug("The application has exited successfully.");
                    Application.Exit(); 
                    Thread.Sleep(2000);
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
                else
                {
                    appLogger.Debug("The phone is rebooting.");
                    Application.Exit();
                    Thread.Sleep(5000);
                    rebootDevice();
                }
        }


      #endregion


        #region Minimize/Back Main Menu Button 


        private void menuQuitApp_Click(object sender, EventArgs e)
        {

            menuQuitApp.Enabled = false;
            menuMainAppActions.Enabled = false;
            string menu_status = "Entering to Botton-Screen-Menu-";

            if (menuQuitApp.Text.CompareTo("Quit") == 0)
            {
                menu_status += "Quit Button Clicked";

                #region Exit Application

                //Show the connect status panel
                label_kernel_status.Text = "...";
                TurnOnPanel(PanelID.CONNECTION);
                Application.DoEvents();


                if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                {

                    #region user confirmed to exit application

                    label_kernel_status.Text = "Ready to exit";
                    appLogger.Debug("user confirmed to quit the application");
                    Application.DoEvents();

                    this.Close();

                    #endregion

                }
                else
                {
                    TurnOnPanel(LastPanel);
                    appLogger.Debug("User decided no to quit application");
                }

                #endregion

            }
            else if (menuQuitApp.Text.CompareTo("Options") == 0) 
            {
                menu_status += "Options Button Clicked";

                menuQuitApp.Text = "Settings";
                menuMainAppActions.Text = "Main Menu";
                TurnOnPanel(PanelID.SETTINGS_OPTIONS);
            }
            else if (menuQuitApp.Text.CompareTo("Settings") == 0)
            {
                 menu_status += "Settings Button Clicked";

                menuQuitApp.Text = "Quit";
                menuMainAppActions.Text = "Back";
                TurnOnPanel(PanelID.SETTINGS_DETAILS);
            }

            appLogger.Debug(menu_status);
            menuQuitApp.Enabled = true;
            menuMainAppActions.Enabled = true;

        }


        private void menuMainAppActions_Click(object sender, EventArgs e)
        {

            menuMainAppActions.Enabled = false;

            try
            {
                if (menuMainAppActions.Text.CompareTo("Minimize") == 0)
                {
                    Minimize_Main_Window();
                    appLogger.Debug("App was minimized");
                }
                else if (menuMainAppActions.Text.CompareTo("Home") == 0) //"Main Menu"
                {
                    TurnOnPanel(PanelID.SWAP);
                    appLogger.Debug("Go to the main sensor status panel");
                }
                else if (menuMainAppActions.Text.CompareTo("Cancel") == 0)
                {
                    sensors_setup_in_panel = false;
                    TurnOnPanel(PanelID.SETTINGS_OPTIONS);
                    appLogger.Debug("Go to the sensor options panel");
                }
                else if (menuMainAppActions.Text.CompareTo("Back") == 0)
                {

                   if ( PanelSettingsDetailed.Visible )
                   {
                        TurnOnPanel(PanelID.SETTINGS_OPTIONS);
                        appLogger.Debug("Go to the sensor options panel");
                   }
                   else if( UploadDataPanel.Visible | SensorPacketsPanel.Visible | SwapPanel.Visible) //!LocationPanel.Visible & !PanelSettingsDetailed.Visible)
                   {
                       TurnOnPanel(PanelID.SETTINGS_DETAILS);
                       appLogger.Debug("Go to the sensor details panel");
                   } 
                   else if (LocationPanel.Visible & panel_location_buttons.Visible)
                        GoToPanel(PanelID.LOCATION_BUTTONS, PanelID.PREPARE_SET);

                   else if ( LocationPanel.Visible & panel_sensor_verification_2.Visible &
                             (panel_sensor_verification_labelID.Text.CompareTo("W") == 0))
                    {
                        GoToPanel(PanelID.VERIFY_W_SENSOR, PanelID.LOCATION_BUTTONS);

                        if (is_change_locations_panel_launched)
                        {

                            menuMainAppActions.Text = "Cancel";
                            menuQuitApp.Text = "";
                        }
                        else
                        {
                            menuMainAppActions.Text = "Back";
                            menuQuitApp.Text = "";
                        }
                    }
                    else if (  LocationPanel.Visible & panel_sensor_verification_2.Visible &
                               (panel_sensor_verification_labelID.Text.CompareTo("A") == 0))
                    {
                        GoToPanel(PanelID.VERIFY_A_SENSOR, PanelID.VERIFY_W_SENSOR);
                        
                        menuMainAppActions.Text = "Back";
                        menuQuitApp.Text = "";
                    }
                    else if (  LocationPanel.Visible & panel_sensor_verification_1.Visible &
                               (textBox_sensor_verification_msg.Text.Contains("SWAP") | textBox_sensor_verification_msg.Text.Contains("LOCATION")))
                    {
                        if (NUMBER_OF_SENSORS == 2)
                            GoToPanel(PanelID.SWAP_COMPLETED, PanelID.VERIFY_A_SENSOR);
                        else if (NUMBER_OF_SENSORS == 1)
                            GoToPanel(PanelID.SWAP_COMPLETED, PanelID.VERIFY_W_SENSOR);
                        else
                            GoToPanel(PanelID.SWAP_COMPLETED, PanelID.LOCATION_BUTTONS);
                            
                        menuMainAppActions.Text = "Back";
                        menuQuitApp.Text = "";
                    }
                }
                else if (menuMainAppActions.Text.CompareTo("Change Set") == 0)
                {

                    if (ChangeSensorSetID())
                        GoToPanel(PanelID.PREPARE_SET, PanelID.PREPARE_SET);

                    appLogger.Debug("Change sensor set button clicked | set changed.");
                }
            }
            catch(Exception ex) 
            {   appLogger.Debug("An exception occurred when minimizing/main menu button clicked. ex: " + ex);   }


            menuMainAppActions.Enabled = true;

        }


        private void Minimize_Main_Window()
        {
            ShowWindow(this.Handle, SW_MINIMIZED);
        }


      #endregion 


        #region Settings Panel Buttons

        //Upload Button
        private void UploadDataActionButton_Click(object sender, EventArgs e)
        {
            UploadDataActionButton.Enabled = false;
            appLogger.Debug("Go to the upload panel");

            //Update Main App Actions Menu
            menuMainAppActions.Text = "Back";
            TurnOnPanel(PanelID.UPLOAD);
            UploadDataActionButton.Enabled = true;
        }

        //Detail Status Button
        private void SensorsDetailStatusButton_Click(object sender, EventArgs e)
        {
            SensorsStatusButton.Enabled = false;
            appLogger.Debug("Go to the sensor status panel");

            //Update Main App Actions Menu
            menuMainAppActions.Text = "Back";
            TurnOnPanel(PanelID.PACKETS);

            SensorsStatusButton.Enabled = true;
        }

     #endregion


        #region Data Uploader
        
        //Upload Button From UploadDataPanel
        private void UploadButton_Click(object sender, EventArgs e)
        {
            UploadRawButton.Enabled = false;
            appLogger.Debug("upload data button clicked");

            if (!Is_DataUploader_Running())
            {
                //Start Data Uploader
                label_upload_data_status.Text = "Starting Raw Data Uploader...";
                label_upload_data_status.ForeColor = Color.Orange;
                Application.DoEvents();

                LaunchDataUploader();

            }
        }


        private void LaunchDataUploader()
        {
            
            try
            {
               
                //Launch the uploader process
                ProcessStartInfo startInfo = new ProcessStartInfo();
                startInfo.WorkingDirectory = Settings._MainWocketsDirectory + "rawdatauploader\\";
                startInfo.FileName = Settings._MainWocketsDirectory + "rawdatauploader\\" + "DataUploader.exe";
                startInfo.UseShellExecute = false;
                _UploaderProcess = System.Diagnostics.Process.Start(startInfo.FileName, "");

                //update status
                if (_UploaderProcess != null)
                {
                    label_upload_data_status.Text = "Uploading Raw Data";
                    label_upload_data_status.ForeColor = Color.Green;
                    UploadRawButton.Enabled = false;

                    appLogger.Debug("Raw data uploader launched successfully.");
                }
                else
                {
                    label_upload_data_status.Text = "The raw data upload couldn't start.";
                    label_upload_data_status.ForeColor = Color.DimGray;
                    UploadRawButton.Enabled = true;

                    appLogger.Debug("Raw data uploader launched couldn't be launched.");
                }

                //TODO: Add an asynchronous sleep here
            }
            catch (Exception ex)
            {
                UploadRawButton.Enabled = true;
                appLogger.Debug("An exception occureed when trying to launch the raw data uploader program. ex: " + ex);
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

                    //update status
                    if (found)
                        appLogger.Debug("Check Processes RawDataUploader | the data uploader is running.");
                    else
                        appLogger.Debug("Check Processes RawDataUploader | the data uploader is NOT running.");

                    return found;
                }
                else
                {
                    appLogger.Debug("Check Processes RawDataUploader | the running processes were not retrieved.");
                    return false; 
                }
            }
            catch (Exception e)
            {
                appLogger.Debug("Check Processes RawDataUploader | an exception occureed when inquiring if the uploader is running. Ex: " + e);
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
                        appLogger.Debug("Check Processes RawDataUploader | the data uploader is running.");
                    else
                        appLogger.Debug("Check Processes RawDataUploader | the data uploader is NOT running.");

                    return found;
                }
                else
                {
                    appLogger.Debug("Check Processes RawDataUploader | the running processes were not retrieved.");
                    return false; 
                }

            }
            catch (Exception ex)
            {
                appLogger.Debug("An exception occureed when inquiring if the data uploader is running, with get process." + ex);
                return false;
            }
        }


     #endregion

     
        #region Log Uploader

        private void InitializeUploadStatusVariables()
        {
            ElapsedTime_LogUpload = TimeSpan.Zero;
            LastLogUploadInvoke = new DateTime();
            LastLogUploadInvoke = DateTime.Now;
            ElapsedTime_DataUpload = TimeSpan.Zero;

           //Initialize Elapsed Time Counter On File Upload Screen
            //textBox_elapsed_time.Visible = false;
            //textBox_elapsed_time.Enabled = false;
            //textBox_elapsed_time.Text = "00h:00m:00s";
        }


        private void UploadLogsButton_Click(object sender, EventArgs e)
        {
            UploadLogsButton.Enabled = false;
            appLogger.Debug("upload logs button clicked");


            if ( !Is_LogUploader_Running() )
            {
                //Start Log Uploader
                label_upload_data_status.Text = "Starting Log Uploader...";
                label_upload_data_status.ForeColor = Color.Orange;
                Application.DoEvents();

                LaunchLogUploader();
            }
        }


        private bool LaunchLogUploader()
        {
            try
            {
                //Launch the uploader process
                ProcessStartInfo startInfo = new ProcessStartInfo();
                startInfo.WorkingDirectory = Settings._MainWocketsDirectory + "loguploader\\";
                startInfo.FileName = Settings._MainWocketsDirectory + "loguploader\\" + "LogUploader.exe";   
                startInfo.UseShellExecute = false;
                _LogUploaderProcess = System.Diagnostics.Process.Start(startInfo.FileName, "");

                //update status
                if ( _LogUploaderProcess != null)
                {
                    label_upload_data_status.Text = "Uploading Data Logs";
                    label_upload_data_status.ForeColor = Color.Green;
                    appLogger.Debug("Check Processes LogDataUploader | the logUploader.exe program was launched.");
                    return true;
                }
                else
                {
                    label_upload_data_status.Text = "The log upload couldn't start";
                    label_upload_data_status.ForeColor = Color.DimGray;
                    appLogger.Debug("Check Processes LogDataUploader | the logUploader.exe program could't start.");
                    return false;
                }

                //TODO: Add an asynchronous sleep here
            }
            catch (Exception ex)
            {
                appLogger.Debug("Check Processes LogDataUploader | an exception occurred when trying to launch the logUploader.exe program. Ex: " + ex);
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
                        appLogger.Debug("Check Processes LogDataUploader | the log uploader is running.");
                        return true;
                    }
                    else
                    {
                        appLogger.Debug("Check Processes LogDataUploader | the log uploader is NOT running.");
                        return false;
                    }
                }
                else
                {
                    appLogger.Debug("Check Processes LogDataUploader | the running processes were not retrieved.");
                    return false; 
                }

            }
            catch (Exception e)
            {
                appLogger.Debug("Check Processes LogDataUploader | an exception occureed when inquiring if the log uploader is running. Ex: " + e);
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
                    {
                        appLogger.Debug("Check Processes LogDataUploader | the log uploader is running.");
                        return true;
                    }
                    else
                    {
                        appLogger.Debug("Check Processes LogDataUploader | the log uploader is NOT running.");
                        return false;
                    }
                }
                else
                {
                    appLogger.Debug("Check Processes LogDataUploader | the running processes were not retrieved.");
                    return false; 
                }
            }
            catch (Exception ex)
            {

                appLogger.Debug("An exception occurred when inquiring if the log uploader is running, with get process." + ex);
                return false;
            }
        }


      #endregion



      #region QA Questionnaire
        
        
        private void LaunchWocketsQuestionarie()
        {
            try
            {
                //Launch the uploader process
                ProcessStartInfo startInfo = new ProcessStartInfo();
                startInfo.WorkingDirectory = Settings._MainWocketsDirectory + "WocketsQA\\";
                startInfo.FileName = Settings._MainWocketsDirectory + "WocketsQA\\" + "WocketsQuestionsAnswers.exe";
                startInfo.UseShellExecute = false;
                System.Diagnostics.Process _ExeProcess = System.Diagnostics.Process.Start(startInfo.FileName, "AppRunMinimized");

                //update status
                if (_ExeProcess != null)
                    appLogger.Debug("Check Processes QA | Wockets Questionarie launched successfully.");
                else
                    appLogger.Debug("Check Processes QA | Wockets Questionarie couldn't be launched.");
            }
            catch (Exception ex)
            {
                appLogger.Debug("Check Processes QA | an exception occureed when trying to launch the wockets questionarie program. ex: " + ex);
            }
        }


        private bool Is_WocketsQuestionarie_Running()
        {
            bool found = false;

            try
            {
                ProcessInfo[] processes = ProcessCE.GetProcesses();

                if (processes != null)
                {

                    for (int i = 0; (i < processes.Length); i++)
                    {
                        if (processes[i].FullPath.IndexOf("WocketsQuestionsAnswers.exe") >= 0)
                        {
                            found = true;
                            break;
                        }
                    }


                    //update status
                    if (found)
                        appLogger.Debug("Check Processes QA | the wockets questionarie QA is running.");
                    else
                        appLogger.Debug("Check Processes QA | the wockets questionarie QA is NOT running.");

                    return found;
                }
                else
                {
                    appLogger.Debug("Check Processes QA | the running processes were not retrieved.");
                    return false;
                }
            }
            catch (Exception e)
            {
                appLogger.Debug("Check Processes QA | an exception occureed when inquiring if the wockets questionarie QA is running. Ex: " + e);
                return false;
            }
        }


        private bool Is_WocketsQuestionarie_Running(out System.Diagnostics.Process uprocess)
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
                        if (processes[i].FullPath.IndexOf("WocketsQuestionsAnswers.exe") >= 0)
                        {
                            uprocess = System.Diagnostics.Process.GetProcessById((int)processes[i].Pid);
                            found = true;
                            break;
                        }
                    }

                    //update status
                    if (found)
                        appLogger.Debug("Check Processes QA | the wockets questionarie QA is running.");
                    else
                        appLogger.Debug("Check Processes QA | the wockets questionarie QA is NOT running.");

                    return found;
                }
                else
                {
                    appLogger.Debug("Check Processes QA | the running processes were not retrieved.");
                    return false;
                }
            }
            catch (Exception ex)
            {
                appLogger.Debug("Check Processes QA | an exception occureed when inquiring if the The wockets questionarie QA is running, with get process." + ex);
                return false;
            }
        }


        private void TerminateWocketsQuestionarie()
        {
            try
            {
                System.Diagnostics.Process questionarie_process = null;
                if (Is_WocketsQuestionarie_Running(out questionarie_process))
                {
                    if (questionarie_process != null)
                    {
                        questionarie_process.Kill();
                        Thread.Sleep(500);
                    }
                }
            }
            catch (Exception e)
            { appLogger.Debug("Check Processes QA | an exception occurred when trying to terminate the wockets questionarie QA process. Ex: " + e.ToString()); }
        }


     #endregion


      #region Elapsed Time Counter & Upload Thread

        public void StartUpdateUploadThread()
        {
            uploadThread = new Thread(new ThreadStart(RunUploadThread));
            uploadThread.Start();
        }


        public void StopUpdateUploadThread()
      {
          if (uploadThread != null)
          { uploadThread.Abort();
            uploadThread = null;
            appLogger.Debug("UpdateUploadThread Monitoring Thread | Stopped");
          }
      }


        //Application Running Elapsed Time
        //private string ElapsedTime = "00days  00h:00m:00s";
        private void RunUploadThread()
        {
          try
          {
              appLogger.Debug("UpdateUploadThread Monitoring Thread | Started");

              while (true)
              {
                  #region commented
                  //TODO: Compute Elapsed Time
                  //TimeSpan elapsed_duration = DateTime.Now.Subtract(Settings._SessionStart);

                  //if (elapsed_duration.Days > 0)
                  //    ElapsedTime = elapsed_duration.Days.ToString("00") + "days  " + elapsed_duration.Hours.ToString("00") + "h:" + elapsed_duration.Minutes.ToString("00") + "m:" + elapsed_duration.Seconds.ToString("00") + "s";
                  //else
                  //    ElapsedTime = elapsed_duration.Hours.ToString("00") + "h:" + elapsed_duration.Minutes.ToString("00") + "m:" + elapsed_duration.Seconds.ToString("00") + "s";
                  #endregion


                  UpdateFilesUploaded();
                  Thread.Sleep(1000);
              }
          }
          catch
          {
              appLogger.Debug("UpdateUploadThread Monitoring Thread | an exception occurred when trying to update the file upload parameters");
          }
      }


     #endregion


      #region File Upload Update Status

        //delegate void UpdateTimeCallback();
        public void UpdateFilesUploaded()
        {
            #region commented

            //if (!disposed)
            //{
            //    if (textBox_elapsed_time.InvokeRequired)
            //    // InvokeRequired required compares the thread ID of the
            //    // calling thread to the thread ID of the creating thread.
            //    // If these threads are different, it returns true.
            //    {
            //        UpdateTimeCallback d = new UpdateTimeCallback(UpdateFilesUploaded);
            //        this.Invoke(d, new object[] { });
            //    }
            //    else
            //    {
            //TODO: Duration Label
            //textBox_elapsed_time.Text = ElapsedTime;
            #endregion

            counter++;


            if (counter == 10) //update every ~10 secs
            {

                #region Determine if the uploader program is still running

                bool is_data_uploaded = false;
                label_upload_data_status.Text = "";

                if (Is_DataUploader_Running())
                {
                    label_upload_data_status.Text += "Raw Data, ";
                    this.UploadRawButton.Enabled = false;
                    is_data_uploaded = true;
                    appLogger.Debug("UpdateUploadThread Monitoring Thread | the raw data and logs uploader processes are running.");
                }
                else
                    this.UploadRawButton.Enabled = true;



                if (Is_LogUploader_Running())
                {
                    label_upload_data_status.Text += "Logs ";
                    this.UploadLogsButton.Enabled = false;
                    is_data_uploaded = true;
                    appLogger.Debug("UpdateUploadThread Monitoring Thread | the logs uploader process is running.");
                }
                else
                    this.UploadLogsButton.Enabled = true;



                if (is_data_uploaded)
                {
                    label_upload_data_status.ForeColor = Color.Green;
                    label_upload_data_status.Text += "Uploading";
                }
                else
                {
                    label_upload_data_status.Text = "...";
                    label_upload_data_status.ForeColor = Color.DimGray;
                }

                #endregion

                counter = 0;
            }


            #region commented
            //this.Invalidate();
            //}
            //}
            #endregion

        }

      #endregion



      #region Reset ACs Registries (COMMENTED)

         //private void ResetUploaderCounters()
         //{
         //     try
         //     {
         //         Core.WRITE_LAST_UPLOAD_FAILEDFILES(0);
         //         Core.WRITE_LAST_UPLOAD_SUCCESSFILES(0);
         //         Core.WRITE_LAST_UPLOAD_NEWFILES(0);
         //     }
         //     catch
         //     {
         //         appLogger.Debug("An exception occurred when trying to reset Uploader counters");
         //     }
         //}

         //private void ResetACsCounters(WocketsController wc)
         //{
         //     try
         //     {
         //         for (int i = 0; (i < wc._Receivers.Count); i++)
         //         {
         //             Core.WRITE_FULL_RECEIVED_COUNT(i, 0);
         //             Core.WRITE_PARTIAL_RECEIVED_COUNT(i, 0);
         //             Core.WRITE_EMPTY_RECEIVED_COUNT(i, 0);
         //             Core.WRITE_RECEIVED_ACs(i, -1);
         //             Core.WRITE_SAVED_ACs(i, -1);
         //         }
         //     }
         //     catch
         //     {
         //         appLogger.Debug("An exception occurred when trying to reset ACs counters");
         //     }
         // }

      #endregion



      #region Thread tracking the sensor connection status

        double WAIT_INTERVAL_LOG_UPLOADER = 60.0; //in minutes
        private int MAX_NSENSORS_TO_UPLOAD = 3;
        //double WAIT_INTERVAL_DATA_UPLOADER= 60.0; //in minutes
        

     private void ACsUpdateTimer_Tick(object sender, EventArgs e)
     {
         
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

                         //if elapsed time > 1min check pkg status
                         if (ElapsedConnectionTime[i].TotalMinutes > 1.0)
                         {
                             #region IF ELAPSED TIME > 1MIN


                             #region Load the AC Counts to Kernel (commented)

                             //if (!received_count_read)
                             //{
                             //    Core.READ_EMPTY_RECEIVED_COUNT();
                             //    Core.READ_FULL_RECEIVED_COUNT();
                             //    Core.READ_PARTIAL_RECEIVED_COUNT();
                             //    Core.READ_RECEIVED_ACs();
                             //    Core.READ_SAVED_ACs();

                             //    received_count_read = true;
                             //}

                             #endregion


                             #region Update the ACs on Panel

                             if (i == 0)
                             {
                                 this.textBox_spanel_ac_full_0.Text = CurrentWockets._Controller._Sensors[i]._Full.ToString();
                                 this.textBox_spanel_ac_partial_0.Text = CurrentWockets._Controller._Sensors[i]._Partial.ToString();
                                 this.textBox_spanel_ac_empty_0.Text = CurrentWockets._Controller._Sensors[i]._Empty.ToString();

                                 this.textBox_spanel_ac_new_0.Text = CurrentWockets._Controller._Sensors[i]._SavedACs + " - " + CurrentWockets._Controller._Sensors[i]._TotalSavedACs;
                                 this.textBox_spanel_ac_last_0.Text = CurrentWockets._Controller._Sensors[i]._ReceivedACs + " - " + CurrentWockets._Controller._Sensors[i]._TotalReceivedACs;
                             }
                             else if (i == 1)
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
                                 else if (i == 1)
                                 {
                                     textBox_sensors_status_1.Text = "Saving Data";
                                     textBox_sensors_status_1.ForeColor = Color.Orange;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_2.Text = "Saving Data";
                                     textBox_sensors_status_2.ForeColor = Color.Orange;
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
                                 else if (i == 1)
                                 {
                                     textBox_sensors_status_1.Text = "Data Lost";
                                     textBox_sensors_status_1.ForeColor = Color.Tomato;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_2.Text = "Data Lost";
                                     textBox_sensors_status_2.ForeColor = Color.Tomato;
                                 }

                                 #endregion

                             }
                             //If the # of packages didn't changed
                             else
                             {

                                 #region Check if packets arrived within 5min & update fields

                                 if (ElapsedConnectionTime[i].TotalMinutes <= 5.0)
                                 {
                                     if (i == 0)
                                     {
                                         textBox_sensors_status_0.Text = "Waiting For Data";
                                         textBox_sensors_status_0.ForeColor = Color.DimGray;
                                     }
                                     else if (i == 1)
                                     {
                                         textBox_sensors_status_1.Text = "Waiting For Data";
                                         textBox_sensors_status_1.ForeColor = Color.DimGray;
                                     }
                                     else
                                     {
                                         textBox_sensors_status_2.Text = "Waiting For Data";
                                         textBox_sensors_status_2.ForeColor = Color.DimGray;
                                     }

                                 }
                                 else
                                 {
                                     if (i == 0)
                                     {
                                         textBox_sensors_status_0.Text = "No Data Received";
                                         textBox_sensors_status_0.ForeColor = Color.Red;
                                     }
                                     else if (i == 1)
                                     {
                                         textBox_sensors_status_1.Text = "No Data Received";
                                         textBox_sensors_status_1.ForeColor = Color.Red;
                                     }
                                     else
                                     {
                                         textBox_sensors_status_2.Text = "No Data Received";
                                         textBox_sensors_status_2.ForeColor = Color.Red;
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
                                 else if (i == 1)
                                 {
                                     textBox_sensors_status_1.Text = "---";
                                     textBox_sensors_status_1.ForeColor = Color.DimGray;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_2.Text = "---";
                                     textBox_sensors_status_2.ForeColor = Color.DimGray;
                                 }

                             }
                             else
                             {
                                 if (i == 0)
                                 {
                                     textBox_sensors_status_0.Text = "Data Received";
                                     textBox_sensors_status_0.ForeColor = Color.Green;
                                 }
                                 else if (i == 1)
                                 {
                                     textBox_sensors_status_1.Text = "Data Received";
                                     textBox_sensors_status_1.ForeColor = Color.Green;
                                 }
                                 else
                                 {
                                     textBox_sensors_status_2.Text = "Data Received";
                                     textBox_sensors_status_2.ForeColor = Color.Green;
                                 }
                             }

                             #endregion
                         }


                     }//ends for loop
                 }//if sensors count >0
             }//if sensors list != null
         }
         catch (Exception ex)
         {
             appLogger.Debug("An exeption occurred when updating/monitoring the Acs counts for connection status. Ex: " + ex.ToString());
         }

        #endregion


         #region Write Event Status To File
         if (swap_event == 1 | restart_event == 1 | locationChanged_event == 1)
         {
             string currentTime = DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss");
             string event_status_log = currentTime + "," + swap_event.ToString() + "," + restart_event.ToString() + "," +
                                       locationChanged_event.ToString() + "," + sensor_set;


             if (CurrentWockets._Controller._Sensors != null)
             {

                 event_status_log += "," + CurrentWockets._Controller._Sensors.Count.ToString();


                 for (int w = 0; w < MAX_NSENSORS_TO_UPLOAD; w++)
                 {

                     if (w < CurrentWockets._Controller._Sensors.Count)
                     {
                         if ((CurrentWockets._Controller._Sensors[w]._Location.CompareTo("null") != 0) &
                             (CurrentWockets._Controller._Sensors[w]._Location.Trim().CompareTo("") != 0))
                         {

                             event_status_log += "," + CurrentWockets._Controller._Sensors[w]._Address + "," +
                                                 CurrentWockets._Controller._Sensors[w]._Location + ",";

                             if (w == 0)
                                 event_status_log += "W";
                             else if (w == 1)
                                 event_status_log += "A";

                         }
                         else
                             event_status_log += ",,,";
                     }
                     else
                         event_status_log += ",,,";

                 }
             }
             else
             {
                 event_status_log += ",0" ;

                 for (int w = 0; w < MAX_NSENSORS_TO_UPLOAD; w++)
                   event_status_log += ",,,";
             }

             //write the events to upload file
             UploadLoggerEvents.Write( event_status_log );
             Thread.Sleep(1000);

             //reset events
             swap_event = restart_event = locationChanged_event = 0;

         }
         #endregion


         #region Determine if the log/data uploader needs to be launched

         try 
         {  
            //Launch the data uploader at midnight once a day
            DateTime current_time = DateTime.Now;

            //Launch log uploader within a time interval
            ElapsedTime_LogUpload = current_time.Subtract(LastLogUploadInvoke);

            if (ElapsedTime_LogUpload.TotalMinutes > WAIT_INTERVAL_LOG_UPLOADER)
            {
                if (!Is_DataUploader_Running() )
                {
                    //bool launch_log_uploader = true;

                    //upload raw data between 1am and 5am
                    if (current_time.Hour >= 1 && current_time.Hour <= 5 & upload_raw_data)
                    {
                        //Core.READ_LAST_UPLOAD_TIME();
                        //ElapsedTime_DataUpload = current_time.Subtract(CurrentWockets._UploadLastTime);

                        //if (ElapsedTime_DataUpload.TotalMinutes > WAIT_INTERVAL_DATA_UPLOADER)
                        //{
                            //if (Is_LogUploader_Running())
                            //{
                            //    TerminateLogUploader();
                            //    Thread.Sleep(1000);
                            //}

                            LaunchDataUploader();
                            //launch_log_uploader = false;
                        //}
                    }
                }

                    //if (launch_log_uploader)
                    //{
                        // if log uploader is NOT running, launch it 
                    if (!Is_LogUploader_Running())
                         LaunchLogUploader();
                    //}
                //}



                LastLogUploadInvoke = current_time;
            }
         }
         catch(Exception ex) 
         {   
             appLogger.Debug("An exeption occurred when invoking the log uploader. Ex: " + ex.ToString());
         }

        #endregion

     }


        private void StartACsUpdater()
        {
            ACsUpdateTimer.Enabled = true;
            appLogger.Debug("Interface Update Thread Timer | Started.");
        }


        private void StopACsUpdater()
        {
            ACsUpdateTimer.Enabled = false;
            appLogger.Debug("Interface Update Thread Timer | Stopped.");

        }

       
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
        private const int KEEP_ALIVE_MESSAGE = 0xA127;


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
               referedForm.Close();
            }
            else if (m.Msg == KEEP_ALIVE_MESSAGE)
            {
                
            }

            //make sure to pass along all messages
            base.WndProc(ref m);
        }


    }


    #endregion


}