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
        //private String app_status = ""; //commented for now until determine if it is necessary to keep this state
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


            #region Read last status (commented for now, not necessary to keep the status)

            //try
            //{
            //    if (File.Exists(Core.KERNEL_PATH + "\\updater_last_status.txt"))
            //    {
            //        StreamReader tr_status = new StreamReader(Core.KERNEL_PATH + "\\updater_last_status.txt");
                    
            //        app_status = tr_status.ReadLine();
            //        string vibrate_mode = tr_status.ReadLine();
            //        string mute_mode    = tr_status.ReadLine();
            //        string volume_mode = tr_status.ReadLine();
            //        #region commented
            //        //string vibrate_mode = tr_status.ReadLine();
            //        //string mute_mode = tr_status.ReadLine();
            //        //string volume_mode = tr_status.ReadLine();
            //        #endregion 

            //        tr_status.Close();


            //        if (this.app_status.CompareTo("") == 0)
            //        {  //this.app_status = "normal_start"; 
            //            this.app_status = "running";
            //        }
            //    }

            //}
            //catch
            //{
            //    //this.app_status = "normal_start";
            //    this.app_status = "running";
            //}

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
           
            
            #region Check MAC addresses updates from master list


            wockets_controller = new Wockets.WocketsController("", "", "");

            LoadSensorsFromMasterList(wockets_controller, sensor_data, this.sensor_set);

            //point kernel to the wockets controller
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

            #endregion


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
            textBox_elapsed_time.Enabled = false;
            textBox_elapsed_time.Text = "00h:00m:00s";

            #endregion
 

            #region Try to connect to kernel, using the loaded settings

            #region Initialize GUI Panels

            InitializePanels();
            TurnOnPanel(PanelID.CONNECTION);
            label_kernel_status.Text = "Loading Application";
            
            #endregion

            //Start the kernel connection sequence
            StartLoadingWocketsToKernel();
            Logger.Debug("Connecting to Kernel in Silent Mode");


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

                            //Stop Update Thread For Data Upload
                            StopUpdateUploadThread();
                            textBox_elapsed_time.Visible = false;
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
                    //Launch the update thread for the data upload
                    textBox_elapsed_time.Visible = true;
                    StartUpdateUploadThread();
                    
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
                    string msg = "Kernel Running";
                    textBox_sensors_status.Text = msg;
                    textBox_sensors_status.ForeColor = Color.Green;

                    //update the sensor status panel
                    textBox_spanel_sensors_status.Text = msg;
                    textBox_spanel_sensors_status.ForeColor = Color.Green;

                    //update fields in main app actions panel
                    textBox_main_sensor_status.Text = msg;
                    textBox_main_sensor_status.ForeColor = Color.Green;
                }
                else
                {
                    string msg = "Kernel Not Running";
                    textBox_sensors_status.Text = msg;
                    textBox_sensors_status.ForeColor = Color.DimGray;

                    //update the sensor status panel
                    textBox_spanel_sensors_status.Text = msg;
                    textBox_spanel_sensors_status.ForeColor = Color.DimGray;

                    //update fields in main app actions panel
                    textBox_main_sensor_status.Text = msg;
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
                #region commented
                //if (app_status.CompareTo("running") == 0)
                //{
                #endregion

                //TODO: monitor the time that takes to receive the disconnect response
                //      to avoid the operation hangs.

                    //Disconnect current sensors set from kernel
                    Core.Disconnect();
                    UpdateMsg("Disconnecting Wockets");
                    Logger.Debug("Sending Disconnect Command to Kernel");

                #region select the sensors according the status is commented for now
                //}
                //else
                //{
                //    UpdateMsg("Swapping Wockets");
                //    Logger.Debug("Start Swapping Sensors in Normal Mode. Kernel Not Connected.");

                //    //TODO: Stop the elapsep time thread

                //    //Dispose the old wockets controller
                //    wockets_controller.Dispose();
                //    wockets_controller = new Wockets.WocketsController("", "", "");


                //    //Determine which set will be used & load the corresponding Xml File
                //    if (this.sensor_set.CompareTo("red") == 0)
                //    {
                //        sensor_set = "green";
                //        wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");
                //    }
                //    else
                //    {
                //        sensor_set = "red";
                //        wockets_controller.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
                //    }


                //    //point the kernel to the wockets controller
                //    CurrentWockets._Controller = wockets_controller;


                //    //TODO: Check if macs against the master list file


                //    //Add the sensors macs to the sensor list
                //    sensors_list.Clear();
                //    for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                //        sensors_list.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);


                //    Thread.Sleep(1000);

                //    #region Hide the connect status panel
                //    //ConnectPanel.Visible = false;
                //    //ConnectPanel.Enabled = false;

                //    ////Show the swap panel
                //    //SwapPanel.BringToFront();
                //    //SwapPanel.Visible = true;
                //    //SwapPanel.Enabled = true;
                //    #endregion

                //    TurnOnPanel(PanelID.SWAP);

                //    //Update the swap interface
                //    Show_Swap_Panel("Disconnected", sensor_set, wockets_controller);

                //}
                #endregion

            }
            catch(Exception ex)
            {
                Logger.Debug("An exception ocurred when trying to disconnect from kernel, after the swap button was clicked. Ex: " + ex);
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
                                try
                                {
                                    Logger.Debug("Ping responsed received");
                                    UpdateMsg("Ping Received");
                                    Core.Register();
                                }
                                catch(Exception ex)
                                {
                                    Logger.Debug("An exception occurred in trying to register app in the kernel. Ex: " + ex); 
                                } 
                            break;

                            case KernelResponse.REGISTERED:
                                try
                                {
                                    Logger.Debug("Registered finished response received");
                                    UpdateMsg("Verify Wockets");
                                    Core.SetSensors(this.sensors_list);
                                }
                                catch(Exception ex)
                                {
                                    Logger.Debug("An exception occurred in trying to set sensors in the kernel. Ex: " + ex); 
                                }
                            break;

                            case KernelResponse.SENSORS_UPDATED:
                                try
                                {
                                    Logger.Debug("Sensors updated response received");
                                    UpdateMsg("Connect Wockets");
                                    Core.Connect(TransmissionMode.Bursty60);
                                }
                                catch (Exception ex)
                                {
                                    Logger.Debug("An exception occurred in trying to connect the sensors to the kernel. Ex: " + ex);
                                }
                            break;

                            case KernelResponse.CONNECTED:
                                try
                                {
                                    Logger.Debug("connected response received");
                                    UpdateMsg("Wockets Connected");

                                    //updates the sensor set used by kernel
                                    try
                                    {
                                        Logger.Debug("start saving app status to files");
                                        StreamWriter wr_sensors = new StreamWriter(Core.KERNEL_PATH + "\\updater_last_set.txt");
                                        wr_sensors.WriteLine(sensor_set);
                                        wr_sensors.Flush();
                                        wr_sensors.Close();  
                                    }
                                    catch (Exception e)
                                    {
                                        Logger.Debug("An exception occurred when trying to save set status to file, after receiving kernel connected response. Ex: " + e);
                                    }


                                    //Update the sensors status variable on the swap panel screen
                                    Show_Swap_Panel("Connected", sensor_set, wockets_controller);
                                    TurnOnPanel(PanelID.SWAP);

                                    //Update the main application menu options
                                    menuMainAppActions.Text = "Main Menu";

                                    //Start the connection status thread 
                                    if (!ACsUpdateTimer.Enabled)
                                        StartACsUpdater();

                                    //Initialize the connection status timer
                                    for (int np = 0; np < wockets_controller._Receivers.Count; np++)
                                        LastPkgTime[np] = DateTime.Now;

                                    Logger.Debug("Connection to wockets procedure finished");
                                }
                                catch (Exception ex)
                                {
                                    Logger.Debug("An exception occurred while executing the kernel connect sequence. Ex: " + ex);
                                }
                            break;


                            case KernelResponse.DISCONNECTED:
                                  try
                                  {
                                      Logger.Debug("Disconnect from wockets response received");    
                                      UpdateMsg("Stopping Kernel");

                                      //Indicate the swap sequence in the status files
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
                                  catch(Exception ex)
                                  {
                                      Logger.Debug("An exception occurred after disconnected from kernel, before rebooting. When trying to save set id to file in the swapping process. Ex: " + ex);
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
                catch(Exception e)
                {
                   Logger.Debug("exception in the main kernel event listener. Ex; " + e);
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

            #region this function is obsolete (commented)
        //delegate void UpdateSensorStatusCallback(string status_msg);
        //private void UpdateSensorStatus(string status_msg)
        //{
        //    try
        //    {
        //        // InvokeRequired required compares the thread ID of the
        //        // calling thread to the thread ID of the creating thread.
        //        // If these threads are different, it returns true.
        //        if (this.InvokeRequired || this.InvokeRequired)
        //        {
        //            UpdateSensorStatusCallback d = new UpdateSensorStatusCallback(UpdateSensorStatus);
        //            this.Invoke(d, new object[] { status_msg });
        //        }
        //        else
        //        {
 
        //            if (status_msg.CompareTo("Connected") == 0)
        //            {
        //                string msg = "Kernel Running";
        //                textBox_sensors_status.Text = msg;
        //                textBox_sensors_status.ForeColor = Color.Green;

        //                //update the sensor status panel
        //                textBox_spanel_sensors_status.Text = msg;
        //                textBox_spanel_sensors_status.ForeColor = Color.Green;

        //                //update fields in main app actions panel
        //                textBox_main_sensor_status.Text = msg;
        //                textBox_main_sensor_status.ForeColor = Color.Green;
        //            }
        //            else if (status_msg.CompareTo("Disconnected") == 0)
        //            {
        //                string msg = "Kernel Not Running";
        //                textBox_sensors_status.Text = msg;
        //                textBox_sensors_status.ForeColor = Color.DimGray;

        //                //update the sensor status panel
        //                textBox_spanel_sensors_status.Text = msg;
        //                textBox_spanel_sensors_status.ForeColor = Color.DimGray;

        //                //update fields in main app actions panel
        //                textBox_main_sensor_status.Text = msg;
        //                textBox_main_sensor_status.ForeColor = Color.DimGray;
        //            }
        //            else
        //            {
        //                textBox_sensors_status.Text = status_msg;
        //                textBox_sensors_status.ForeColor = Color.DimGray;

        //                //update the sensor status panel
        //                textBox_spanel_sensors_status.Text = status_msg;
        //                textBox_spanel_sensors_status.ForeColor = Color.DimGray;

        //                //update fields in main app actions panel
        //                textBox_main_sensor_status.Text = status_msg;
        //                textBox_main_sensor_status.ForeColor = Color.DimGray;
        //            }

        //            Application.DoEvents();
        //        }
        //    }
        //    catch
        //    { 
        //        //Fail updating the sensors connection status
        //    }
        //}
        #endregion
        #endregion


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

       private void menuQuitApp_Click(object sender, EventArgs e)
        {
            menuQuitApp.Enabled = false;
            menuMainAppActions.Enabled = false;
            Logger.Debug("Quit Button Clicked");

            #region Exit Application

            //Show the connect status panel
            label_kernel_status.Text = "...";
            TurnOnPanel(PanelID.CONNECTION);
            Application.DoEvents();


            if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {

                #region user confirmed to exit application

                label_kernel_status.Text = "Exiting Application";
                Logger.Debug("user confirmed to quit the application");
                Application.DoEvents();
                TerminateApp();

                #endregion

            }
            else
            {
                TurnOnPanel(LastPanel);
                Logger.Debug("User decided no to quit the application");
            }

            #endregion

            menuQuitApp.Enabled = true;
            menuMainAppActions.Enabled = true;
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
                //TODO: Here try more agressive methods to stop the kernel
                Logger.Debug("An exception occurred when trying to terminate kernel. ex:" + e);
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
            { return false; }     
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
            try
            {
                System.Diagnostics.Process kernel_process = null;

                if (Is_Kernel_Running(out kernel_process))
                {
                    if (kernel_process != null)
                       kernel_process.Kill();
                }
            }
            catch(Exception e)
            {
                Logger.Debug("An exception occurred when trying to kill the kernel process. Ex: " + e);
            }
        }


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
            { Logger.Debug("An exception occurred when trying to terminate the log uploader. Ex: " + e); }
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
            catch
            { Logger.Debug("An exception occurred when trying to terminate the data uploader."); }  
        }


        public void TerminateApp()
        {
            try
            {
                Logger.Debug("Starting to quit application");

                //Stop Update Upload Thread if running
                StopUpdateUploadThread();

                //Stop status monitoring thread
                StopACsUpdater();

                //Wait for the system to stabilize and check that threads have finished
                Thread.Sleep(1000);

                //Termine uploaders if running
                TerminateDataUploader();
                TerminateLogUploader();

                //Terminate the kernel, if running
                if (!TerminateKernel()) //=== if (!Core._KernalStarted)
                    Logger.Debug("Failed to terminate kernel, exection when forcing to quit");

                //Close the hidden window 
                this.messageWindow.Dispose();

                Application.Exit();
            }
            catch
            { Logger.Debug("An exception occurred when trying to quit the application"); }
            
        }


        private void WocketsMainForm_Closing(object sender, CancelEventArgs e)
        {
            TerminateApp();   
        }
        

        private void WocketsMainForm_Closed(object sender, EventArgs e)
        {
                if (!is_rebooting)
                {
                    Logger.Debug("The application has quit successfully.");
                    KillKernel();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
                else
                {
                    Logger.Debug("The phone is rebooting.");
                    rebootDevice();
                }
        }


      #endregion


      #region Minimize/Main Menu Button 

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
                    TurnOnPanel(PanelID.MAIN);
                    Logger.Debug("Go to the main menu panel");
                }
            }
            catch(Exception ex) 
            {   Logger.Debug("An exception occurred when minimizing/main menu button clicked. ex: " + ex);   }   
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
                Logger.Debug("An exception occureed when inquiring if the uploader is running. Ex: " + e);
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
                Logger.Debug("An exception occureed when trying to launch the logUploader.exe program. Ex: " + ex);
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
                Logger.Debug("An exception occureed when inquiring if the log uploader is running. Ex: " + e);
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
            uploadThread = null;
            Logger.Debug("upload monitor thread stopped");
          }
      }

      private void RunUploadThread()
      {
          try
          {
              Logger.Debug("upload monitor thread started");

              while (true)
              {
                  //TODO: Compute Elapsed Time
                  TimeSpan elapsed_duration = DateTime.Now.Subtract(Settings._SessionStart);

                  if (elapsed_duration.Days > 0)
                      ElapsedTime = elapsed_duration.Days.ToString("00") + "days  " + elapsed_duration.Hours.ToString("00") + "h:" + elapsed_duration.Minutes.ToString("00") + "m:" + elapsed_duration.Seconds.ToString("00") + "s";
                  else
                      ElapsedTime = elapsed_duration.Hours.ToString("00") + "h:" + elapsed_duration.Minutes.ToString("00") + "m:" + elapsed_duration.Seconds.ToString("00") + "s";


                  UpdateFilesUploaded();
                  Thread.Sleep(1000);
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

                  if (counter == 6) //enter every 6 secs
                  {
                     #region Determine if the uploader program is still running

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

                     counter = 0;
                  }

                  this.Invalidate();
              }
          }
      }

      #endregion


      #region Reset ACs Registries

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

       #endregion


      #region Thread tracking the sensor connection status

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
                //referedForm.TerminateApp();
                referedForm.Close();
            }

            //make sure to pass along all messages
            base.WndProc(ref m);
        }


    }


    #endregion


}