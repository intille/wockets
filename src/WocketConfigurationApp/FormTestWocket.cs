using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Threading;

using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
 
using Wockets;
using Wockets.Data.Configuration;
using Wockets.Decoders;
using Wockets.Decoders.Accelerometers;
using Wockets.Receivers;
using Wockets.Sensors;
using Wockets.Sensors.Accelerometers;
using Wockets.Data.Commands;
using Wockets.Data.Responses;


namespace WocketConfigurationApp
{
    public partial class FormTestWocket : Form
    {

        #region Declare Variables

        //---- Bluetooth & Wockets ----
        BluetoothDeviceInfo wocket;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        WocketsController wc;

        //---- Commands ---------------
        private string current_command = "";

       
        #region commented
        //private string cur_tr_mode = "";
        //private int cur_sampling_rate = 90;
        //private string cur_sensitivity = "";
        //private int cur_power_down = 90;
        //private bool is_sensordata_valid = false;
        #endregion 


        //----- calibration panel variables  ------------
        private double[] xyzP = new double[3] { 0.0, 0.0, 0.0 };
        private double[] xyzN = new double[3] { 0.0, 0.0, 0.0 };
        private double[] xyzSTD = new double[3] { 0.0, 0.0, 0.0 };

        public static string NEEDED_FILES_PATH = "C:\\Data\\Project\\Google Code\\GoogleCode version 3\\bin\\NeededFiles\\";
        public static string CALIBRATIONS_DIRECTORY = NEEDED_FILES_PATH + "images\\calibrations\\";
        Image[] calibrationImages;
        int calibration_step = -1;


        //------ Battery Calibration Variables  -------
        public static string BATTERY_DIRECTORY = NEEDED_FILES_PATH + "images\\battery\\";
        private Image[] bat_calibrationImages;
        private int bat_calibration_step = -1;
        bool is_test_finished = true;

        private DateTime BTCAL_StartTime;
        private DateTime BTCAL_CurTime;
        private DateTime BTCAL_TotalTime;
        private TimeSpan BTCAL_OffTime;
        private DateTime BTCAL_StopOffTime;


        //100%, 80%, 60%, 40%, 20%, 10%
        private double[] target_bat_cal_values = new double[6] { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 };
        private double[] bat_cal_values = new double[6] { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 };

        private int CAL_UPDATE_SECS = 10000;
        
        private int StartBTLevel = 0;
        private int CurBTLevel = 0;

        private TextWriter log_file = null;
        private string log_filename = "";
        private string OUTPUT_DIRECTORY = "";

        string[] TestResults = new String[20];


        //------ Sampling Rate Test ------------
        private int sr_test_step = -1;
        private TimeSpan ElapsedTime = TimeSpan.Zero;
        private TimeSpan MaxTestTime = new TimeSpan(0, 5, 0);  // 5 minutes

        private int SR = 0;
        private int CUMSR = 0;
        private int SRCount = 0;


        #region commented
        //----- Data Collection ---------------
        //private const int CALIBRATION_SAMPLES = 1200;
        //private int[][] samples;
        //private double time = 0;
        //private int currentIndex = -1;

        //private int sampleCounter = 0;
        //private int numOfSamples = 0;

        //private DateTime startTime;
        //private DateTime endTime;
        //private bool isTracking = false;

        //private Thread aPollingThread = null;
        #endregion 


        #endregion


        #region Initialize

        public FormTestWocket(BluetoothDeviceInfo wocket)
        {
            InitializeComponent();

            //Copy parameters to loacal variables
            this.wocket = wocket;
            this.Text = "Wocket (" + wocket.DeviceAddress.ToString() + ")";

            //Load the parameters saved on the bluetoothinfo device
            this.info_cmd_value_name.Text = wocket.DeviceName;
            this.info_cmd_value_mac.Text = wocket.DeviceAddress.ToString();
            this.panel_status_texbox.Text = "";

            //disable battery timer
            this.test_timer.Enabled = false;
            this.test_timer.Stop();


            //load status panels
            this.panel_status.Visible = true;

            //load calibration panel
            this.panel_calibration.Visible = false;

            //calibration images
            this.calibrationImages = new Image[7];

            for (int i = 0; (i < 6); i++)
                this.calibrationImages[i] = (Image)new Bitmap(CALIBRATIONS_DIRECTORY + "calibration" + (i + 1) + ".png");

            //bat calibration images
            this.bat_calibrationImages = new Image[6];

            for (int i = 0; (i < 6); i++)
                this.bat_calibrationImages[i] = (Image)new Bitmap(BATTERY_DIRECTORY + "battery" + (i + 1) + ".png");

           //clean calibration values
            current_command = "calibration";
            clean_calibration_values(true);

            current_command = "battery_calibration";
            clean_calibration_values(true);

           
            //Initialize Test Results
            TestResults[0] = ",calibration,x+,0.0";
            TestResults[1] = ",calibration,x-,0.0";
            TestResults[2] = ",calibration,xstd,0.0";
            TestResults[3] = ",calibration,y+,0.0";
            TestResults[4] = ",calibration,y-,0.0";
            TestResults[5] = ",calibration,ystd,0.0";
            TestResults[6] = ",calibration,z+,0.0";
            TestResults[7] = ",calibration,z-,0.0";
            TestResults[8] = ",calibration,zstd,0.0";
            TestResults[9] = "";
            TestResults[10] = ",sampling_rate,SR,0";
            TestResults[11] = "";
            TestResults[12] = ",battery_calibration,100%,0";
            TestResults[13] = ",battery_calibration,80%,0";
            TestResults[14] = ",battery_calibration,60%,0";
            TestResults[15] = ",battery_calibration,40%,0";
            TestResults[16] = ",battery_calibration,20%,0";
            TestResults[17] = ",battery_calibration,10%,0";
            TestResults[18] = "";
            TestResults[19] = ",rssi_quality,RSSI,0";

            //output directory
            OUTPUT_DIRECTORY = Environment.GetFolderPath(Environment.SpecialFolder.Desktop) +
                               "\\WocketsTest\\Session_" + String.Format("{0:MMddyy-HHmmss}", DateTime.Now) + "\\";

            if (!Directory.Exists(OUTPUT_DIRECTORY))
            { Directory.CreateDirectory(OUTPUT_DIRECTORY); }

        }

        private void Form2_Load(object sender, EventArgs e)
        {
            //wocket controller object
            InitializeWocket();

            //commands
            LoadWocketsParameters();
        }

        private void LoadWocketsParameters()
        {
            Command cmd;

            //-----  Read the commands when the form is loaded  ------------------------
            cmd = new GET_FV();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_HV();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_PC();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_BT();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_BP();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_BTCAL();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_CAL();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_SEN();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_TM();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_SR();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            cmd = new GET_PDT();
            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

  
            //-----------------------------------------------------------------------

        
        }

        private void InitializeWocket()
        {
            //Load Wocket Parameters
            WocketsConfiguration configuration = new WocketsConfiguration();
            CurrentWockets._Configuration = configuration;

            wc = new WocketsController("", "", "");
            CurrentWockets._Controller = wc;

            wc._Receivers = new ReceiverList();
            wc._Decoders = new DecoderList();
            wc._Sensors = new SensorList();
            wc._Receivers.Add(new RFCOMMReceiver());
            wc._Decoders.Add(new WocketsDecoder());
            wc._Sensors.Add(new Wocket());

            ((RFCOMMReceiver)wc._Receivers[0])._Address = this.wocket.DeviceAddress.ToString();
            wc._Receivers[0]._ID = 0;
            wc._Decoders[0]._ID = 0;
            wc._Sensors[0]._Receiver = wc._Receivers[0];
            wc._Sensors[0]._Decoder = wc._Decoders[0];
            ((Accelerometer)wc._Sensors[0])._Max = 1024;
            ((Accelerometer)wc._Sensors[0])._Min = 0;
            wc._Sensors[0]._Loaded = true;

            //initialize circular data buffer
            //cbuffer = new Wockets.Data.Accelerometers.AccelerationData[MaxSamples];
            cbuffer = new double[MaxSamples ,3];


            //------------ suscriptions --------------
            //battery level
            wc._Decoders[0].Subscribe(ResponseTypes.BL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //sampling rate
            wc._Decoders[0].Subscribe(ResponseTypes.SR_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //transmission mode
            wc._Decoders[0].Subscribe(ResponseTypes.TM_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //battery percent
            wc._Decoders[0].Subscribe(ResponseTypes.BP_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //sensor sensitivity mode
            wc._Decoders[0].Subscribe(ResponseTypes.SENS_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //calibration mode
            wc._Decoders[0].Subscribe(ResponseTypes.CAL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //packets count
            wc._Decoders[0].Subscribe(ResponseTypes.PC_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //power down timeout
            wc._Decoders[0].Subscribe(ResponseTypes.PDT_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //battery calibration
            wc._Decoders[0].Subscribe(ResponseTypes.BTCAL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //hardware version
            wc._Decoders[0].Subscribe(ResponseTypes.HV_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //firmware version
            wc._Decoders[0].Subscribe(ResponseTypes.FV_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            

            //---- initialize wocket controller -------
            wc.Initialize();
  
        }

        #endregion Initialize


        #region Timers: Recconect & Battery


        private void timer1_Tick(object sender, EventArgs e)
        {

            if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Connected)
            {
                #region Connected

                if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Data)
                { this.label_connect_status.Text = "Connected: Data Mode"; }
                else
                { this.label_connect_status.Text = "Connected: Command Mode"; }


                //update progress bars here

                #endregion 
            }
            else
            {
                #region Disconnected & Reconnecting

                    if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Disconnected)
                    {
                        this.label_connect_status.Text = "Disconnected";
                    }
                    else if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Reconnecting)
                    {
                        this.label_connect_status.Text = "Reconnecting";
                    }


                    #region Interrupt the test
                    
                    /*
                    if (current_command.CompareTo("battery_calibration") == 0)
                    {   //Interrupt the test
                        bat_calibration_step = 1;
                    }
                    if (current_command.CompareTo("sampling_rate") == 0)
                    {   //Interrupt the test
                       sr_test_step = 1;
                    }
                    if (current_command.CompareTo("calibration") == 0)
                    {   //Interrupt the test
                        calibration_step = 1;
                    }

                    //process the stop step
                    process_calibration();

                    cal_panel_label_status.Text = " The wocket is Disconnected.\r\n The test has STOPPED. \r\n";
                    cal_panel_button_ok.Enabled = false;
                    */

                    #endregion Interrup the test

                #endregion
            }


            //temporal for testing
            #region Update the progress indicators
            
            if ((current_command.Trim().CompareTo("") != 0) &&
                 (!is_test_finished))
            {
                //update battery progress bar
                int val = 0;
                Math.DivRem(cal_panel_progressBar.Value + 10, 100, out val);
                cal_panel_progressBar.Value = val;

                //update elapsed time field = time.now - start_time
                ElapsedTime = ((DateTime)DateTime.Now).Subtract(BTCAL_StartTime);
                ElapsedTime = ElapsedTime.Subtract(BTCAL_OffTime);

                cal_panel_bat_label_elapTime.Text = ElapsedTime.ToString().Split('.')[0];
            }

            #endregion

        }


        private void test_timer_Tick(object sender, EventArgs e)
        {
            
            
            //if (label_connect_status.Text.Contains("Connected:"))
            //{
                if ((current_command.CompareTo("batery_calibration") != 0) &&
                         (!is_test_finished))
                {

                    #region Send battery level command

                    BTCAL_CurTime = DateTime.Now;
                    TimeSpan TimeDiff = BTCAL_CurTime.Subtract(BTCAL_TotalTime);

                    if (TimeDiff.TotalMilliseconds >= CAL_UPDATE_SECS)
                    {
                        //update the time variables
                        BTCAL_TotalTime = BTCAL_CurTime;


                        // send the corresponding command
                        if ((current_command.CompareTo("battery_calibration") == 0))
                        {
                            GET_BT cmd = new GET_BT();
                            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                        }
                        if ((current_command.CompareTo("sampling_rate") == 0))
                        {
                            GET_SR cmd = new GET_SR();
                            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                        }

                    }

                    #endregion
                }
                else if ((current_command.CompareTo("calibration") == 0) &&
                         (is_test_finished) && (!is_reading) )
                {
                    StopReading();
                    cal_panel_button_ok.Enabled = true;
                    process_calibration();
                }

            //}
        }




        #endregion


        #region Delegates Callback

        delegate void UpdateResponseCallback(object e);

        private void ResponseCallback(object e)
        {

            if (this.InvokeRequired)
            {
                UpdateResponseCallback d = new UpdateResponseCallback(ResponseCallback);
                this.Invoke(d, new object[] { e });
            }
            else
            {

                //------------------ Decode the command responses --------------------------
                Response response = (Wockets.Data.Responses.Response)e;
                switch (response._Type)
                {
                    //ACC calibration 
                    case ResponseTypes.CAL_RSP:
                        info_cmd_value_WKTCalibration.Text = ((CAL_RSP)response)._X1G.ToString() + " " + ((CAL_RSP)response)._XN1G.ToString() + " " + ((CAL_RSP)response)._Y1G.ToString() + " " + ((CAL_RSP)response)._YN1G.ToString() + " " + ((CAL_RSP)response)._Z1G.ToString() + " " + ((CAL_RSP)response)._ZN1G.ToString();
                        break;
                    //battery level
                    case ResponseTypes.BL_RSP:
                        //info_cmd_value_battery_level.Text = ((BL_RSP)response)._BatteryLevel.ToString();
                        process_bat_level_response(response);
                        break;
                    //Sampling Rate
                    case ResponseTypes.SR_RSP:
                        //info_cmd_value_SRQuality.Text = ((SR_RSP)response)._Version.ToString();
                        process_sr_response(response);
                        break;
                    case ResponseTypes.BP_RSP:
                        info_cmd_value_BTQuality.Text = ((BP_RSP)response)._Percent.ToString() + "%";
                        break;
                    case ResponseTypes.PC_RSP:
                        info_cmd_value_RSSIQuality.Text = ((PC_RSP)response)._Count.ToString();
                        break;
                   case ResponseTypes.BTCAL_RSP:
                       info_cmd_value_BTCalibration.Text = ((BTCAL_RSP)response)._CAL100.ToString() + " " + ((BTCAL_RSP)response)._CAL80.ToString() + " " + ((BTCAL_RSP)response)._CAL60.ToString() + " " + ((BTCAL_RSP)response)._CAL40.ToString() + " " + ((BTCAL_RSP)response)._CAL20.ToString() + " " + ((BTCAL_RSP)response)._CAL10.ToString();
                        break;
                  default:
                        break;
                }

                this.Refresh();
            }
        }

        private void process_bat_level_response(Response bt_response)
        { 

            if( (current_command.CompareTo("battery_calibration") == 0) 
                && (!is_test_finished) )
            {
                CurBTLevel = ((BL_RSP)bt_response)._BatteryLevel;

                //Get BatLevel at 100%
                if( CurBTLevel > StartBTLevel ) 
                {
                    StartBTLevel = CurBTLevel;
                    cal_panel_bat_100.Text = CurBTLevel.ToString();

                    //Determine the % for the target battery values
                    bat_cal_values[0] = CurBTLevel; //%100
                    target_bat_cal_values[0] = CurBTLevel; //%100
                    target_bat_cal_values[1] = Math.Floor((double)CurBTLevel * 0.80); //%80
                    target_bat_cal_values[2] = Math.Floor((double)CurBTLevel * 0.60); //%60
                    target_bat_cal_values[3] = Math.Floor((double)CurBTLevel * 0.40); //%40
                    target_bat_cal_values[4] = Math.Floor((double)CurBTLevel * 0.20); //%20
                    target_bat_cal_values[5] = Math.Floor((double)CurBTLevel * 0.10); //%10

                    pictureBox_calibration.Image = bat_calibrationImages[0];
                }
                //Get BatLevel at 80%
                else if (CurBTLevel < target_bat_cal_values[1] )
                {
                    bat_cal_values[1] = CurBTLevel;
                    cal_panel_bat_80.Text = CurBTLevel.ToString();

                    pictureBox_calibration.Image = bat_calibrationImages[1];
                }
                //Get BatLevel at 60%
                else if (CurBTLevel < target_bat_cal_values[2])
                {
                    bat_cal_values[2] = CurBTLevel;
                    cal_panel_bat_60.Text = CurBTLevel.ToString();

                    pictureBox_calibration.Image = bat_calibrationImages[2];
                }
                //Get BatLevel at 40%
                else if (CurBTLevel < target_bat_cal_values[3])
                {
                    bat_cal_values[3] = CurBTLevel;
                    cal_panel_bat_40.Text = CurBTLevel.ToString();

                    pictureBox_calibration.Image = bat_calibrationImages[3];
                }
                //Get BatLevel at 20%
                else if (CurBTLevel < target_bat_cal_values[4])
                {
                    bat_cal_values[4] = CurBTLevel;
                    cal_panel_bat_20.Text = CurBTLevel.ToString();

                    pictureBox_calibration.Image = bat_calibrationImages[4];
                }
                //Get BatLevel at 10%
                else if (CurBTLevel < target_bat_cal_values[5])
                {
                    bat_cal_values[5] = CurBTLevel;
                    cal_panel_bat_10.Text = CurBTLevel.ToString();
               
                    //Finish the test
                    is_test_finished = true;
                    bat_calibration_step = 3;
                    process_calibration();

                    pictureBox_calibration.Image = bat_calibrationImages[5];
                }

                if (log_file != null)
                {
                    DateTime timenow = DateTime.Now;
                    log_file.WriteLine( timenow.ToShortDateString()+" "+ String.Format("{0:HH:mm:ss.fff}", timenow) + "," + CurBTLevel.ToString());
                }

            }
            

        }

        private void process_sr_response(Response w_response)
        {
            

            if ((current_command.CompareTo("sampling_rate") == 0)
                && (!is_test_finished))
            {
                int sr_response = ((SR_RSP)w_response)._SamplingRate;
                CUMSR = CUMSR + sr_response;
                SRCount = SRCount + 1;

                if (log_file != null)
                {
                    //Log the data 
                    DateTime timenow = DateTime.Now;
                    log_file.WriteLine(timenow.ToShortDateString() + " " + String.Format("{0:HH:mm:ss.fff}", timenow) + "," + sr_response.ToString());
                }

                //Stop the test reached the maximum elapsed time 
                TimeSpan diff = ElapsedTime.Subtract(MaxTestTime);
                    

                if ( diff.TotalSeconds >= 0.0 )
                {   
                    //Compute the total SR
                    SR = (int)Math.Floor((double)(CUMSR/SRCount));

                    //Finish the test
                    is_test_finished = true;
                    sr_test_step = 3;
                    process_calibration();
                }
            }

        }


        #endregion


        #region MenuStrip

        private void commandToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Data)
            {
                /*((RFCOMMReceiver)wc._Receivers[0])._TimeoutEnabled = false;
                CurrentWockets._Controller._Decoders[0]._Mode = DecoderModes.Command;
                Command c = new EnterCommandMode();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(c._Bytes);*/
            }
        }

        private void dataToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Command)
            {
                /*CurrentWockets._Controller._Decoders[0]._Mode = DecoderModes.Data;
                Command c = new ExitCommandMode();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(c._Bytes);*/
            }

        }

        #endregion 


        #region Plot Signal

            Form3 plotterForm = null;
            private void plotToolStripMenuItem_Click(object sender, EventArgs e)
            {
                plotData();
            }

            private void plotData()
            {

              if (CurrentWockets._Controller != null)
                {
                    if (!plotToolStripMenuItem.Checked)
                    {
                        if ((plotterForm == null) || (!plotterForm.Visible))
                            plotterForm = new Form3();
                        if (!plotterForm.Visible)
                            plotterForm.Show();
                    }
                    else
                    {

                        if (plotterForm != null)
                        {
                            plotterForm.Close();
                            plotterForm = null;
                        }
                    }
                }

            }

        #endregion


        #region Text Fields Functions
        
        private void change_status_field(Label cur_label,TextBox cur_field, Keys value, string cur_cmd)
        {

            if (current_command.CompareTo("all") != 0)
            {
                if (current_command.Trim().CompareTo("") != 0)
                {
                    if( current_command.CompareTo(cur_cmd) !=0 )
                    {
                        cleanup_fields(current_command);
                        Application.DoEvents();
                    }
                }

                if (value == Keys.Enter)
                {
                    current_command = cur_cmd;
                    cur_field.BackColor = Color.WhiteSmoke;
                    cur_field.ForeColor = Color.Black;
                    cur_label.ForeColor = Color.WhiteSmoke;

                }
                else if (value == Keys.Escape)
                {
                    current_command = "";
                    cur_field.BackColor = Color.DimGray;
                    cur_field.ForeColor = Color.White;
                    cur_label.ForeColor = Color.Orange;
                }
            }

        }

        private void change_status_field(Label cur_label, ComboBox cur_field, Keys value, string cur_cmd)
        {

            if (current_command.CompareTo("all") != 0)
            {
                if (current_command.Trim().CompareTo("") != 0)
                {
                    cleanup_fields(current_command);
                    Application.DoEvents();

                }

                if (value == Keys.Enter)
                {
                    current_command = cur_cmd;
                    cur_field.BackColor = Color.WhiteSmoke;
                    cur_field.ForeColor = Color.Black;
                    cur_label.ForeColor = Color.WhiteSmoke;

                }
                else if (value == Keys.Escape)
                {
                    current_command = "";
                    cur_field.BackColor = Color.DimGray;
                    cur_field.ForeColor = Color.White;
                    cur_label.ForeColor = Color.Orange;
                }
            }

        }

        private void cleanup_fields(string cmd)
        {
            if (current_command.CompareTo("all") != 0)
            {
                switch (cmd)
                {
                    case "sampling_rate":
                        current_command = "";
                        info_cmd_value_SRQuality.BackColor = Color.DimGray;
                        info_cmd_value_SRQuality.ForeColor = Color.White;
                        info_cmd_label_SRQuality.ForeColor = Color.Orange;
                        break;
                    case "packet_count":
                        current_command = "";
                        info_cmd_value_RSSIQuality.BackColor = Color.DimGray;
                        info_cmd_value_RSSIQuality.ForeColor = Color.White;
                        info_cmd_label_RSSI_Quality.ForeColor = Color.Orange;
                        break;
                    case "battery_level":
                        current_command = "";
                        info_cmd_value_TRQuality.BackColor = Color.DimGray;
                        info_cmd_value_TRQuality.ForeColor = Color.White;
                        info_cmd_label_TRQuality.ForeColor = Color.Orange;
                        break;
                    case "battery_percent":
                        current_command = "";
                        info_cmd_value_BTQuality.BackColor = Color.DimGray;
                        info_cmd_value_BTQuality.ForeColor = Color.White;
                        info_cmd_label_BTQuality.ForeColor = Color.Orange;
                        break;
                    case "battery_calibration":
                        current_command = "";
                        info_cmd_value_BTCalibration.BackColor = Color.DimGray;
                        info_cmd_value_BTCalibration.ForeColor = Color.White;
                        info_cmd_label_BTCalibration.ForeColor = Color.Orange;
                        break;
                    case "calibration":
                        current_command = "";
                        info_cmd_value_WKTCalibration.BackColor = Color.DimGray;
                        info_cmd_value_WKTCalibration.ForeColor = Color.White;
                        info_cmd_label_WKTCalibration.ForeColor = Color.Orange;
                        break;
                    
                }
            }
        }

        private void disable_all_fields()
        { 
             current_command = "";

               
              //"sampling_rate":
                  info_cmd_value_SRQuality.BackColor = Color.DimGray;
                  info_cmd_value_SRQuality.ForeColor = Color.White;
                  info_cmd_label_SRQuality.ForeColor = Color.Orange;
                  
              //"packet_count":
                  info_cmd_value_RSSIQuality.BackColor = Color.DimGray;
                  info_cmd_value_RSSIQuality.ForeColor = Color.White;
                  info_cmd_label_RSSI_Quality.ForeColor = Color.Orange;
                 
              //"battery_level":
                  info_cmd_value_TRQuality.BackColor = Color.DimGray;
                  info_cmd_value_TRQuality.ForeColor = Color.White;
                  info_cmd_label_TRQuality.ForeColor = Color.Orange;
                  
              //"battery_percent":
                  info_cmd_value_BTQuality.BackColor= Color.DimGray;
                  info_cmd_value_BTQuality.ForeColor = Color.White;
                  info_cmd_label_BTQuality.ForeColor = Color.Orange;
                  
             //"battery_calibration":
                  info_cmd_value_BTCalibration.BackColor = Color.DimGray;
                  info_cmd_value_BTCalibration.ForeColor = Color.White;
                  info_cmd_label_BTCalibration.ForeColor = Color.Orange;
             
            //"calibration":
                  info_cmd_value_WKTCalibration.BackColor = Color.DimGray;
                  info_cmd_value_WKTCalibration.ForeColor = Color.White;
                  info_cmd_label_WKTCalibration.ForeColor = Color.Orange;
            
           
                  
        }

        private void enable_all_fields()
        {
            current_command = "all";

          
            //"sampling_rate":
            info_cmd_value_SRQuality.BackColor = Color.WhiteSmoke;
            info_cmd_value_SRQuality.ForeColor = Color.Black;
            info_cmd_label_SRQuality.ForeColor = Color.WhiteSmoke;

            //"packet_count":
            info_cmd_value_RSSIQuality.BackColor = Color.WhiteSmoke;
            info_cmd_value_RSSIQuality.ForeColor = Color.Black;
            info_cmd_label_RSSI_Quality.ForeColor = Color.WhiteSmoke;

            //"battery_level":
            info_cmd_value_TRQuality.BackColor = Color.WhiteSmoke;
            info_cmd_value_TRQuality.ForeColor = Color.Black;
            info_cmd_label_TRQuality.ForeColor = Color.WhiteSmoke;

            //"battery_percent":
            info_cmd_value_BTQuality.BackColor = Color.WhiteSmoke;
            info_cmd_value_BTQuality.ForeColor = Color.Black;
            info_cmd_label_BTQuality.ForeColor = Color.WhiteSmoke;

            //"battery_calibration":
            info_cmd_value_BTCalibration.BackColor = Color.WhiteSmoke;
            info_cmd_value_BTCalibration.ForeColor = Color.Black;
            info_cmd_label_BTCalibration.ForeColor = Color.WhiteSmoke;

            //"calibration":
            info_cmd_value_WKTCalibration.BackColor = Color.WhiteSmoke;
            info_cmd_value_WKTCalibration.ForeColor = Color.Black;
            info_cmd_label_WKTCalibration.ForeColor = Color.WhiteSmoke;

            
        }

        private void info_panel_clean_text_fields()
        {
            info_cmd_value_TRQuality.Text = "";
            info_cmd_value_BTQuality.Text = "";
            
            info_cmd_value_WKTCalibration.Text = "";
            info_cmd_value_RSSIQuality.Text = "";
            
            info_cmd_value_BTCalibration.Text = "";
            info_cmd_value_SRQuality.Text = "";
        }

        #endregion


        #region EVENTS

        private void info_cmd_value_swversion_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_SRQuality,info_cmd_value_SRQuality, e.KeyCode, "sampling_rate");

        }

       
        private void info_cmd_value_pkt_count_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_RSSI_Quality,info_cmd_value_RSSIQuality,e.KeyCode, "packet_count");
        }


       private void info_cmd_value_battery_level_KeyDown(object sender, KeyEventArgs e)
       {
            change_status_field(info_cmd_label_TRQuality,info_cmd_value_TRQuality, e.KeyCode, "battery_level");
       }

       private void info_cmd_value_btpercent_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_BTQuality,info_cmd_value_BTQuality, e.KeyCode, "battery_percent");
       }

       private void info_cmd_value_btcalibration_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_BTCalibration,info_cmd_value_BTCalibration, e.KeyCode, "battery_calibration");
       }

       private void info_cmd_value_calibration_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_WKTCalibration,info_cmd_value_WKTCalibration, e.KeyCode, "calibration");
       }

      
        #endregion


        #region Main Buttons

       private void checkBox_LoadAll_CheckedChanged(object sender, EventArgs e)
       {
           if (checkBox_LoadAll.Checked)
           {  //button_load.Enabled = true; 
               enable_all_fields();
           }
           else
           {
               //button_load.Enabled = false;
               disable_all_fields();
           }
       }
    
       private void Load_button_Click(object sender, EventArgs e)
       {
           button_load.Enabled = false;
           Application.DoEvents();



           if (checkBox_LoadAll.Checked && (current_command.CompareTo("all") == 0))
           {
               info_panel_clean_text_fields();
               Application.DoEvents();

               LoadWocketsParameters();
           }
           else
           {
               Command cmd;
               switch (current_command)
               {
                  
                   case "sampling_rate":
                       info_cmd_value_SRQuality.Text = "";
                       Application.DoEvents();
                       cmd = new GET_SR();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "packet_count":
                       info_cmd_value_RSSIQuality.Text = "";
                       Application.DoEvents();
                       cmd = new GET_PC();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_level":
                       info_cmd_value_TRQuality.Text = "";
                       Application.DoEvents();
                       cmd = new GET_BT();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_percent":
                       info_cmd_value_BTQuality.Text = "";
                       Application.DoEvents();
                       cmd = new GET_BP();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_calibration":
                       info_cmd_value_BTCalibration.Text = "";
                       Application.DoEvents();
                       cmd = new GET_BTCAL();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "calibration":
                       info_cmd_value_WKTCalibration.Text = "";
                       Application.DoEvents();
                       cmd = new GET_CAL();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
               }
           }

           button_load.Enabled = true;

       }

       private void button_start_test_Click(object sender, EventArgs e)
       {
           if (!checkBox_LoadAll.Checked)
           {

               button_start_test.Enabled = false;
               button_to_xml.Enabled = false;


               if (current_command.CompareTo("calibration") == 0)
               {
                   #region Calibration
                   //Plot Data
                   plotToolStripMenuItem.Checked = false;
                   plotData();


                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_WKTCalibration.Text;
                   cal_panel_cmd_label.Text = "Path";
                   cal_panel_entry_path.Text = "";
                   cal_panel_label_status.Text = "Position the wocket as shown in the picture.\r\n" +
                                                 "Then, click START to begin the calibration.\r\n"  +
                                                 "During the test, keep the wocket in the same position.";
                   
                   cal_panel_button_ok.Text = "Start";

                   cal_panel_bat_values.Visible = false;
                   cal_panel_cal_values.Visible = false;

                   //progress bar
                   cal_panel_progressBar.Visible = false;


                   //buttons
                   button_load.Enabled = false;
                   button_finish.Enabled = false;

                 
                   //calibration panel
                   panel_calibration.Visible = true;
                   //is_sensordata_valid = false;

                   //picture box
                   pictureBox_calibration.Size = new Size(358, 240);
                   pictureBox_calibration.Visible = true;
                   pictureBox_calibration.Image = calibrationImages[0];

                   //Hide select folder fields
                   cal_panel_entry_path.Enabled = false;
                   cal_panel_entry_path.Visible = false;

                   cal_panel_cmd_label.Visible = false;

                   cal_panel_button_browse.Enabled = true;
                   cal_panel_button_browse.Visible = false;


                   //clean panel parameters
                   panel_status_texbox.Text = "";
                   panel_status.Visible = false;
                   
                   
                   //start calibration steps
                   calibration_step = 0;
                   cal_panel_button_ok.Enabled = true;
                   info_cmd_value_WKTCalibration.Text = "Calibrating ...";
                   clean_calibration_values(true);
                  

                   #endregion Calibration
               }
               else if (current_command.CompareTo("battery_calibration") == 0)
               {
                   #region Battery Calibration
                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_BTCalibration.Text;
                   cal_panel_cmd_label.Text = "Path";
                   cal_panel_entry_path.Text = "";
                   cal_panel_label_status.Text = "Make sure that the battery is fully charged.\r\n" + 
                                                 "Press START to begin the battery calibration.";

                   cal_panel_button_ok.Text = "Start";

                   //Battery Log File
                   log_filename = OUTPUT_DIRECTORY + wocket.DeviceAddress.ToString().Substring(7) + "_" +
                                  "BAT_Log.txt";  
                   log_file = new StreamWriter(log_filename);


                   //progress bar
                   cal_panel_progressBar.Visible = true;
                   cal_panel_progressBar.Value = 0;
                   

                   //clean panel parameters
                   panel_status_texbox.Text = "";
                   panel_status.Visible = false;

                   //Hide Value Panels
                   cal_panel_bat_values.Visible = false;
                   cal_panel_cal_values.Visible = false;

                   //Hide select folder fields
                   cal_panel_entry_path.Enabled = false;
                   cal_panel_entry_path.Visible = false;
                   cal_panel_cmd_label.Visible = false;
                   cal_panel_button_browse.Enabled = true;
                   cal_panel_button_browse.Visible = false;


                   //calibration panel
                   panel_calibration.Visible = true;
                   //is_sensordata_valid = false;

                   //picture box
                   pictureBox_calibration.Size = new Size(135, 240);
                   pictureBox_calibration.Visible = true;

                   //start battery calibration steps
                   bat_calibration_step = 0;
                   cal_panel_button_ok.Enabled = true;
                   info_cmd_value_BTCalibration.Text = "Calibrating Battery";
                   clean_calibration_values(true);
                   pictureBox_calibration.Image = null;

                   #endregion BAT Calibration
               }
               else if (current_command.CompareTo("sampling_rate") == 0)
               {

                   #region Sampling Rate Test
                   
                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_SRQuality.Text;
                   cal_panel_cmd_label.Text = "Path";
                   cal_panel_entry_path.Text = "";
                   cal_panel_label_status.Text = "Place the wocket in a surface with NO MOVEMENT or VIBRATION as shown in the picture.\r\n" +
                                                 "When ready, click START to begin the test.\r\n";
                                                 
                   cal_panel_button_ok.Text = "Start";

                   //Sampling Rate Log Filei
                   log_filename = OUTPUT_DIRECTORY +
                                  wocket.DeviceAddress.ToString().Substring(7) + "_" +
                                  "SR_Log.txt"; 
                   log_file = new StreamWriter(log_filename);


                   //progress bar
                   cal_panel_progressBar.Visible = true;
                   cal_panel_progressBar.Value = 0;

                   //picture box
                   pictureBox_calibration.Image = calibrationImages[4];
                   pictureBox_calibration.Visible = true;
                   
                   //clean panel parameters
                   panel_status_texbox.Text = "";
                   panel_status.Visible = false;

                   //Hide Value Panels
                   cal_panel_bat_values.Visible = false;
                   cal_panel_cal_values.Visible = false;

                   //Hide select folder fields
                   cal_panel_entry_path.Enabled = false;
                   cal_panel_entry_path.Visible = false;
                   cal_panel_cmd_label.Visible = false;
                   cal_panel_button_browse.Enabled = true;
                   cal_panel_button_browse.Visible = false;


                   //calibration panel
                   panel_calibration.Visible = true;
                    //is_sensordata_valid = false;


                   //start battery calibration steps
                   sr_test_step = 0;
                   cal_panel_button_ok.Enabled = true;
                   info_cmd_value_SRQuality.Text = "Testing Sampling Rate...";
                   

                   #endregion Sampling Rate Test

               }
               else
               {
                   button_start_test.Enabled = true;
               }

           }
       }



       private void button_to_xml_Click(object sender, EventArgs e)
       {
           button_to_xml.Enabled = false;

           if (!write_results_to_xml(wc))
           {
               Console.WriteLine("Problem when writing to the xml file.");
               panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" + 
                                          "Problem when writing to the xml file.";
           }
           else
           {    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           DateTime.Now.ToString() + " : " + "The xml file was sucessfully written.";

               //write to the test file
               if (!write_results_to_file(TestResults))
               {
                   Console.WriteLine("Problem when writing to the test file.");
                   panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                              "Problem when writing to the test file.";
               }
               else
               {
                   panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                              DateTime.Now.ToString() + " : " + "The test file was sucessfully written.";
               }
           }

           button_to_xml.Enabled = true;

       }
  
       #endregion


        #region Panel Buttons
       
        private void cal_panel_button_ok_Click(object sender, EventArgs e)
        {
            process_calibration();
        }

        private bool calibrate_wocket(int cal_axis, out double cal_value)
        {
            bool is_axis_calibrated = true;
           

            if (cal_axis == 0)
            {
                //Calibration for X +1G axis
                cal_value = 700.0;
                is_axis_calibrated = true;
            }

            cal_value = 700.0;
            return is_axis_calibrated;

        }

        private void cal_panel_button_cancel_Click(object sender, EventArgs e)
        {
            //restore status panel
            restore_status_panel();

            if (current_command.CompareTo("calibration") == 0)
            { info_cmd_value_WKTCalibration.Text = "No Calibrated"; }
            else if (current_command.CompareTo("battery_calibration") == 0)
            { info_cmd_value_BTCalibration.Text = "No Calibrated"; }
            else if (current_command.CompareTo("sampling_rate") == 0)
            { info_cmd_value_SRQuality.Text = "No Tested"; }
   
        }

        private void cal_panel_button_browse_Click(object sender, EventArgs e)
        {
              try
              {
                  //check the path selected in the textbox
                  this.folderBrowserDialog1.ShowNewFolderButton = false;
                  


                  if (cal_panel_entry_path.Text.Trim().CompareTo("") != 0)
                  {
                      if (Directory.Exists(cal_panel_entry_path.Text))
                      {
                          this.folderBrowserDialog1.SelectedPath = cal_panel_entry_path.Text.ToString();
                      }
                     
                  }
                  

                  //check the path selected in the dialog
                  DialogResult result = this.folderBrowserDialog1.ShowDialog();
                  

                  if (result == DialogResult.OK)
                  {
                      string fullPath = this.folderBrowserDialog1.SelectedPath;
                      
                      cal_panel_entry_path.Text = fullPath;

                      if (cal_panel_entry_path.Text.Trim().CompareTo("") == 0)
                      {
                          cal_panel_label_status.Text = "Please provide a valid path";
                      }
                      else
                      {
                          #region Commented
                          //WocketsController wc_xml = new WocketsController("", "", "");
                          //wc_xml.FromXML(fullPath);
                          //Accelerometer acc_sensor = (Accelerometer)wc_xml._Sensors[0];
                  
                          //if it is a valid sensordata file with calibration values
                          //open the sensordata file and get the calibration values 
                          //fullPath = fullPath + "\\SensorData.xml";
                          //if (Directory.Exists(fullPath))
                          //{
                          //    if (current_command.CompareTo("calibration") == 0)
                          //    {
                          //        //update the calibration fields
                          //        cal_panel_x1g.Text = acc_sensor._X1g.ToString();
                          //        cal_panel_xn1g.Text = acc_sensor._Xn1g.ToString();
                          //        cal_panel_xstd.Text = acc_sensor._XStd.ToString();

                          //        cal_panel_y1g.Text = acc_sensor._Y1g.ToString();
                          //        cal_panel_yn1g.Text = acc_sensor._Yn1g.ToString();
                          //        cal_panel_ystd.Text = acc_sensor._YStd.ToString();

                          //        cal_panel_z1g.Text = acc_sensor._Z1g.ToString();
                          //        cal_panel_zn1g.Text = acc_sensor._Zn1g.ToString();
                          //        cal_panel_zstd.Text = acc_sensor._ZStd.ToString();

                          //        //load the fields
                          //        xyzP[0] = acc_sensor._X1g;
                          //        xyzP[1] = acc_sensor._Y1g;
                          //        xyzP[2] = acc_sensor._Z1g;

                          //        xyzN[0] = acc_sensor._Xn1g;
                          //        xyzN[1] = acc_sensor._Yn1g;
                          //        xyzN[2] = acc_sensor._Zn1g;

                          //        xyzSTD[0] = acc_sensor._XStd;
                          //        xyzSTD[1] = acc_sensor._YStd;
                          //        xyzSTD[2] = acc_sensor._ZStd;


                          //        //write the status to screen
                          //        cal_panel_label_status.Text = "The sensordata file is valid. You can set the CAL values.";
                          //        is_sensordata_valid = true;

                          //    }
                          //    else if (current_command.CompareTo("battery_calibration") == 0)
                          //    {
                          //        // it is a valid sensordata file with calibration values
                          //        //open the battery calibration file and get the cal values   
                          //        cal_panel_label_status.Text = "The battery calibration file is valid. You can set the CAL values.";
                          //        is_sensordata_valid = true;
                          //    }

                          //}
                          //else
                          //{
                          //    cal_panel_label_status.Text = "The sensordata file is NOT valid. Please try again or click CANCEL to exit the calibration.";
                          //}

                          ////dispose xml wockets controller
                          //acc_sensor.Dispose();
                          //wc_xml.Dispose();
                          #endregion 
                      }
                  }

              } // end try
              catch (Exception err)
              {
                  Console.WriteLine(err.Message);
              }


        }

        #endregion Buttons


        #region Process Calibration Functions 
        
        
        #region commented

        /*
        private void process_calibration()
        {
            if (current_command.CompareTo("calibration") == 0)
            {
                #region Wocket Calibration

                if (calibration_step == 0)
                {
                    #region Calibrate X +1G

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating X +1G...\r\n" + 
                                                  "Keep the wocket in the position shown in the picture.";
                    cal_panel_cal_values.Visible = true;
                    Application.DoEvents();

                    //calibrate wocket
                    if (!calibrate_wocket(calibration_step, out xyzP[0]))
                    {
                        calibration_step = 0;
                        cal_panel_button_ok.Enabled = true;
                        cal_panel_label_status.Text = "Problem calibrating X +1G axis. Please check the wocket and try again.";
                        cal_panel_x1g.Text = "";
                        return;
                    }

                    //Pass to the next step
                    calibration_step = 1;
                    pictureBox_calibration.Image = calibrationImages[1];
                    cal_panel_x1g.Text = xyzP[0].ToString();
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = "X+1G axis has been calibrated. Place the wocket in the new position as shown in the picture. Then, click Next to continue.";

                    #endregion
                }
                else if (calibration_step == 1)
                {

                    #region Calibrate X -1G

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating X -1G... Keep the wocket in the position shown in the picture.";
                    Application.DoEvents();

                    //calibrate wocket
                    if (!calibrate_wocket(calibration_step, out xyzN[0]))
                    {
                        calibration_step = 1;
                        cal_panel_button_ok.Enabled = true;
                        cal_panel_label_status.Text = "Problem calibrating X -1G axis. Please check the wocket and try again.";
                        cal_panel_xn1g.Text = "";
                        return;
                    }

                    //Pass to the next step
                    calibration_step = 2;
                    pictureBox_calibration.Image = calibrationImages[2];
                    cal_panel_xn1g.Text = xyzN[0].ToString();
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = "Finished calibrating X-1G axis. Place the wocket in the new position as shown in the picture. Then, click Next to continue.";

                    #endregion

                }
                else if (calibration_step == 2)
                {

                    #region Calibrate Y +1G

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Y+1G... Keep the wocket in the position shown in the picture.";
                    Application.DoEvents();

                    //calibrate wocket
                    if (!calibrate_wocket(calibration_step, out xyzP[1]))
                    {
                        calibration_step = 2;
                        cal_panel_button_ok.Enabled = true;
                        cal_panel_label_status.Text = "Problem calibrating Y+1G axis. Please check the wocket and try again.";
                        cal_panel_y1g.Text = "";
                        return;
                    }

                    //Pass to the next step
                    calibration_step = 3;
                    pictureBox_calibration.Image = calibrationImages[3];
                    cal_panel_y1g.Text = xyzP[1].ToString();
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = "Finished calibrating Y+1G axis. Place the wocket in the new position as shown in the picture. Then, click Next to continue.";

                    #endregion

                }
                else if (calibration_step == 3)
                {

                    #region Calibrate Y -1G

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Y-1G... Keep the wocket in the position shown in the picture.";
                    Application.DoEvents();

                    //calibrate wocket
                    if (!calibrate_wocket(calibration_step, out xyzN[1]))
                    {
                        calibration_step = 3;
                        cal_panel_button_ok.Enabled = true;
                        cal_panel_label_status.Text = "Problem calibrating Y-1G axis. Please check the wocket and try again.";
                        cal_panel_yn1g.Text = "";
                        return;
                    }

                    //Pass to the next step
                    calibration_step = 4;
                    pictureBox_calibration.Image = calibrationImages[4];
                    cal_panel_yn1g.Text = xyzN[1].ToString();
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = "Finished calibrating Y-1G axis. Place the wocket in the new position as shown in the picture. Then, click Next to continue.";

                    #endregion

                }
                else if (calibration_step == 4)
                {

                    #region Calibrate Z +1G

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Z+1G... Keep the wocket in the position shown in the picture.";
                    Application.DoEvents();

                    //calibrate wocket
                    if (!calibrate_wocket(calibration_step, out xyzP[2]))
                    {
                        calibration_step = 4;
                        cal_panel_button_ok.Enabled = true;
                        cal_panel_label_status.Text = "Problem calibrating Z+1G axis. Please check the wocket and try again.";
                        cal_panel_z1g.Text = "";
                        return;
                    }

                    //Pass to the next step
                    calibration_step = 5;
                    pictureBox_calibration.Image = calibrationImages[5];
                    cal_panel_z1g.Text = xyzP[2].ToString();
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = "Finished calibrating Z+1G axis. Place the wocket in the new position as shown in the picture. Then, click Next to continue.";

                    #endregion

                }
                else if (calibration_step == 5)
                {

                    #region Calibrate Z -1G

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Z-1G... Keep the wocket in the position shown in the picture.";
                    Application.DoEvents();

                    //calibrate wocket
                    if (!calibrate_wocket(calibration_step, out xyzN[2]))
                    {
                        calibration_step = 5;
                        cal_panel_button_ok.Enabled = true;
                        cal_panel_label_status.Text = "Problem calibrating Z-1G axis. Please check the wocket and try again.";
                        cal_panel_zn1g.Text = "";
                        return;
                    }

                    //Finish the calibration process
                    //Determine the axis standard deviations
                    calibration_step = 6;
                    pictureBox_calibration.Visible = false;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_zn1g.Text = xyzN[2].ToString();
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = "Finished the calibration process. Select the path where you want to save the calibration values. Then, click Save.";


                    //show select folder button
                    cal_panel_entry_path.Enabled = true;
                    cal_panel_entry_path.Visible = true;

                    cal_panel_cmd_label.Visible = true;

                    cal_panel_button_browse.Enabled = true;
                    cal_panel_button_browse.Visible = true;

                    #endregion


                }
                else if (calibration_step == 6)
                {

                    #region Save Calibration Values

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = "Please select the folder where you want to save the SensorData.xml file.";
                    Application.DoEvents();

                    #region Commented
                    //string path = cal_panel_entry_path.Text;
                    //string filename = "SensorData_" + wocket.DeviceAddress.ToString().Substring(7) + ".xml";

                    //if (path.Trim().CompareTo("") == 0)
                    //{
                    //    path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);
                    //}
                    //else if (!Directory.Exists(path))
                    //{
                    //    path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);
                    //}


                    //// Save the calibration values to File
                    //path = path + "\\WocketsConfiguration\\" + filename;

                    //save_calibration_to_file(wc, path);
                    #endregion 


                    //Get the current time
                    DateTime timenow = DateTime.Now;

                    //save results
                    string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                                   String.Format("{0:HH:mm:ss}", timenow);

                    //Save values to the test results string
                    TestResults[0] = stime + ",calibration,x+,"   + xyzP[0].ToString();
                    TestResults[1] = stime + ",calibration,x-,"   + xyzN[0].ToString();
                    TestResults[2] = stime + ",calibration,xstd," + xyzSTD[0].ToString();
                    TestResults[3] = stime + ",calibration,y+,"   + xyzP[1].ToString();
                    TestResults[4] = stime + ",calibration,y-,"   + xyzN[1].ToString();
                    TestResults[5] = stime + ",calibration,ystd," + xyzSTD[1].ToString();
                    TestResults[6] = stime + ",calibration,z+,"   + xyzP[2].ToString();
                    TestResults[7] = stime + ",calibration,z-,"   + xyzN[2].ToString();
                    TestResults[8] = stime + ",calibration,zstd," + xyzSTD[2].ToString();


                    //---- Finish the calibration process ------
                    // Determine the axis standard deviations
                    calibration_step = -1;
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();

                    
                    //update the test status
                    info_cmd_value_WKTCalibration.Text = "Calibrated on " + String.Format("{0:HH:mm:ss}", timenow);

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Calibration Test Finished.";


                    #endregion

                }

                #endregion Calibration
            }
            else if (current_command.CompareTo("battery_calibration") == 0)
            {
                #region Battery Calibration

                //Initialize Battery Calibration test
                if (bat_calibration_step == 0)
                {
                    #region Start Calibration

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Calibrating Battery Values...";
                    cal_panel_bat_values.Visible = true;
                    cal_panel_bat_values_percent.Visible = true;
                    Application.DoEvents();

                    // start battery calibration & initialize time counters
                    is_test_finished = false;
                    BTCAL_OffTime = TimeSpan.Zero;
                    BTCAL_StartTime = DateTime.Now;
                    cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);
                    
                    //Enable Timer
                    timer_battery.Enabled = true;
                    timer_battery.Start();

                    //Pass to the next step
                    bat_calibration_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The battery test has started.\r\n Click CANCEL if you want to exit the test.";
                    
                    #endregion

                } //Pause/Stop test
                else if (bat_calibration_step == 1)
                {

                    #region STOP Battery CAL test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "START";
                    cal_panel_label_status.Text = " The battery test has PAUSED.\r\n Click START if you want to resume.\r\n Click CANCEL if you want to exit the test.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;
                    BTCAL_StopOffTime = DateTime.Now;

                    //Restart the CAL test
                    bat_calibration_step = 2;
                    cal_panel_button_ok.Enabled = true;

                    #endregion
                }
                //Restart Calibration test
                else if (bat_calibration_step == 2)
                {
                    #region Resume Calibration

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Calibrating Battery Values...";
                    cal_panel_bat_values.Visible = true;
                    Application.DoEvents();

                    // start battery calibration
                    is_test_finished = false;
                    //BTCAL_OffTime = TimeSpan.Zero;
                    //BTCAL_StartTime = DateTime.Now;
                    //cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);
                    BTCAL_OffTime = BTCAL_OffTime.Add(DateTime.Now.Subtract(BTCAL_StopOffTime));


                    //Pass to the next step
                    bat_calibration_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The battery test is RUNNING.\r\n Click CANCEL if you want to exit the test.";

                    #endregion 

                }
                else if (bat_calibration_step == 3)
                {

                    #region Finish the Battery CAL test & Show Browse Folder

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = "Please select the folder where you want to save the SensorData.xml file.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;

                    //Pass to the next step
                    bat_calibration_step = 4;
                    cal_panel_button_ok.Enabled = true;

                    #endregion

                }
                else if (bat_calibration_step == 4)
                {

                    #region Save Battery Calibration Values

                    //stop battery calibration
                    is_test_finished = true;
                    DateTime timenow = DateTime.Now;

                    #region Commented
                    ////take the path from the file field
                    //string path = cal_panel_entry_path.Text;
                    //string filename = "SensorData_" + wocket.DeviceAddress.ToString().Substring(7) + ".xml";


                    //if (path.Trim().CompareTo("") == 0)
                    //{
                    //    path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);
                    //}
                    //else if (!Directory.Exists(path))
                    //{
                    //    path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);
                    //}


                    //// Save the calibration values to File
                    //path = path + "\\WocketsConfiguration\\" + filename;

                    ////save_battery_calibration_to_file(wc, path);
                    #endregion 

                    //save results
                    string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                                   String.Format("{0:HH:mm:ss}", timenow);

                    //Save values to the test results string
                    TestResults[12] = stime + ",battery_calibration,100%," + bat_cal_values[0].ToString();
                    TestResults[13] = stime + ",battery_calibration,80%,"  + bat_cal_values[1].ToString();
                    TestResults[14] = stime + ",battery_calibration,60%,"  + bat_cal_values[2].ToString();
                    TestResults[15] = stime + ",battery_calibration,40%,"  + bat_cal_values[3].ToString();
                    TestResults[16] = stime + ",battery_calibration,20%,"  + bat_cal_values[4].ToString();
                    TestResults[17] = stime + ",battery_calibration,10%,"  + bat_cal_values[5].ToString();


                    //Finish the test
                    bat_calibration_step = -1;
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();

                    //update the test status
                    info_cmd_value_BTCalibration.Text = "Calibrated on " + String.Format("{0:HH:mm:ss}");

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Battery Calibration Test Finished.";



                    #endregion

                }

                #endregion Battery Calibration

            }
            else if (current_command.CompareTo("sampling_rate") == 0)
            {
                #region Sampling Rate Test

                //Initialize Sampling Rate test
                if (sr_test_step == 0)
                {
                    #region Start Test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Testing Sampling Rate...";
                    cal_panel_bat_values.Visible = true;
                    cal_panel_bat_values_percent.Visible = false;
                    Application.DoEvents();

                    // start battery calibration & initialize time counters
                    is_test_finished = false;
                    BTCAL_OffTime = TimeSpan.Zero;
                    BTCAL_StartTime = DateTime.Now;
                    cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);
                    SR = 0;
                    CUMSR = 0;
                    SRCount = 0;

                    //Enable Timer
                    timer_battery.Enabled = true;
                    timer_battery.Start();

                    //Pass to the next step
                    sr_test_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The test has started.\r\n Click CANCEL if you want to exit.";
                    
                    #endregion

                } //Pause/Stop test
                else if (sr_test_step == 1)
                {

                    #region STOP SR test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "START";
                    cal_panel_label_status.Text = " The test has PAUSED.\r\n Click START if you want to resume.\r\n Click CANCEL if you want to exit.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;
                    BTCAL_StopOffTime = DateTime.Now;

                    //Restart the CAL test
                    sr_test_step = 2;
                    cal_panel_button_ok.Enabled = true;

                    #endregion
                }
                //Restart Calibration test
                else if (sr_test_step == 2)
                {
                    #region Resume Test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Testing Sampling Rate...";
                    cal_panel_bat_values.Visible = true;
                    cal_panel_bat_values_percent.Visible = false;
                    Application.DoEvents();

                    // start battery calibration
                    is_test_finished = false;
                    BTCAL_OffTime = BTCAL_OffTime.Add(DateTime.Now.Subtract(BTCAL_StopOffTime));


                    //Pass to the next step
                    sr_test_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The test is RUNNING.\r\n Click CANCEL if you want to exit.";

                    #endregion

                }
                else if ( sr_test_step == 3)
                {

                    #region Finish the test & Save the values

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = " The test has FINISHED.\r\n Please click SAVE to exit and keep the results.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;

                    //Pass to the next step
                    sr_test_step = 4;
                    cal_panel_button_ok.Enabled = true;

                    #endregion

                }
                else if (sr_test_step == 4)
                {

                    #region Save Battery Calibration Values

                    //stop the test
                    is_test_finished = true;
                    DateTime timenow = DateTime.Now;

                    #region Commented
                    
                    ////take the path from the file field
                    //string path = cal_panel_entry_path.Text;
                    //string filename = "SensorData_" + wocket.DeviceAddress.ToString().Substring(7) + ".xml";

                    //if (path.Trim().CompareTo("") == 0)
                    //{ path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop); }
                    //else if (!Directory.Exists(path))
                    //{ path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);}

                    //// Save the calibration values to File
                    //path = path + "\\WocketsConfiguration\\" + filename;

                    //save_sampling_rate_to_file(wc, path);
                    
                    #endregion

                    //save results
                    TestResults[10] = String.Format("{0:MM-dd-yy}", timenow) + " " +
                                      String.Format("{0:HH:mm:ss}", timenow) + ",sampling_rate,SR," +
                                      SR.ToString();

                    //reset parameters
                    sr_test_step = -1;
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();

                    //update the test status
                    info_cmd_value_SRQuality.Text = "Tested on " + String.Format("{0:HH:mm:ss}", timenow);

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Sampling Rate Test Finished.";



                    #endregion

                }

                #endregion Sampling Rate Test

            }
        }
        */
        
        #endregion 



        private void start_axis_calibration(string axis_name, bool compute_std)
        {
            cal_panel_button_ok.Enabled = false;
            cal_panel_button_ok.Text = "OK";
            cal_panel_label_status.Text = "Calibrating " + axis_name + "...\r\n" +
                                          "Keep the wocket in the same position.";
            
            //values for panel
            cal_panel_cal_values.Visible = true;

            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;

            //pictureBox Calibration
            pictureBox_calibration.Visible = true;


            // start calibration & initialize time counters
            is_test_finished = false;
            BTCAL_OffTime = TimeSpan.Zero;
            BTCAL_StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);


            //Flag that determines if the axis standard deviations need to be computed
            if (compute_std)
                CALIBRATE_STD = true;
              

            //Enable timer
            test_timer.Enabled = true;
            test_timer.Start();


            //Start the reading thread for calibration
            StartReading();

        }


        private string stop_axis_calibration(string axis_name)
        {
            string calibration_result = "";

            cal_panel_button_ok.Enabled = true;
            cal_panel_button_ok.Text = "Continue";
            cal_panel_label_status.Text = "The axis " + axis_name + " calibration has finished.\r\n";
                                            

            //pause test
            is_test_finished = true;

            //update progres bar 
            cal_panel_progressBar.Value = 100;

            //disable timer
            test_timer.Stop();
            test_timer.Enabled = false;

            
            //Get the computed variables
            if (compute_calibration_stats(axis_name, out calibration_result) == 0)
            {
                cal_panel_label_status.Text = cal_panel_label_status.Text +
                                              "The calibration data was collected successfully.";
               //pass to the next step
                calibration_step++;
            }
            else
            {
                cal_panel_label_status.Text = cal_panel_label_status.Text +
                                              "The calibration data was NOT collected successfully.";
                
                //perform the calibration again
                calibration_step --;
            }


            //show the std dev results
            if (CALIBRATE_STD)
            {
                cal_panel_xstd.Text = String.Format("{0:0.00}", xyzSTD[0]);
                cal_panel_ystd.Text = String.Format("{0:0.00}", xyzSTD[1]);
                cal_panel_zstd.Text = String.Format("{0:0.00}", xyzSTD[2]);
            }


            //reset the compute std. dev. flag
            CALIBRATE_STD = false;


            return calibration_result;

        }


        private void position_axis_calibration(string axis_name, int image_number)
        {
            //cal_panel_button_ok.Enabled = false;
            cal_panel_button_ok.Text = "Start";
            cal_panel_label_status.Text = "To start calibrating the "+ axis_name + " axis,\r\n" + 
                                          "place the wocket as shown in the picture.\r\n" +
                                          "When ready, click START.";

            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;

            //clean time counters labels
            cal_panel_bat_label_elapTime.Text = "";
            cal_panel_bat_label_startTime.Text = "";

            //update the image
            pictureBox_calibration.Image = calibrationImages[image_number];

            //update calibration step
            calibration_step++;

        }


        private void process_calibration()
        {
            if (current_command.CompareTo("calibration") == 0)
            {

                #region Wocket Calibration

                if (calibration_step == 0)
                {
                    #region Start Calibrate X +1G
                    #region commented
                    /*
                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "Calibrating X +1G...\r\n" +
                                                  "Keep the wocket in the position shown in the picture.";
                    cal_panel_cal_values.Visible = true;

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //pictureBox Calibration
                    pictureBox_calibration.Visible = true;


                    // start battery calibration & initialize time counters
                    is_test_finished = false;
                    BTCAL_OffTime = TimeSpan.Zero;
                    BTCAL_StartTime = DateTime.Now;
                    cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);

                    //Enable timer
                    test_timer.Enabled = true;
                    test_timer.Start();
                     
                   //Start the read ACC for calibration
                   StartReading(); 
                     
                     
                    */


                    //--- clean up the mean and std variables

                    //--- enable-start calibration timer
                    
                    //--- within the timer call the calibration function
                        ////calibrate wocket
                        //when calibration process finishes, set the next step (calibration_step = 1)
                        //if (!calibrate_wocket(calibration_step, out xyzP[0]))
                        //{
                        //    calibration_step = 0;
                        //    cal_panel_button_ok.Enabled = true;
                        //    cal_panel_label_status.Text = "Problem calibrating X +1G axis. Please check the wocket and try again.";
                        //    cal_panel_x1g.Text = "";
                        //    return;
                    //}
                    #endregion 
                    #endregion

                    start_axis_calibration("X +G", false);
            
                }
                else if(calibration_step == 1)
                {
                    
                    #region Stop Calibrate X +1G

                    #region commented
                    /*
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "X+1G axis has been calibrated.\r\n" + 
                                                  "Click OK to continue...";

                    //update the calibrated variable
                    cal_panel_x1g.Text = xyzP[0].ToString();
                    
                    //pause test
                    is_test_finished = true;

                    //update progres bar 
                    cal_panel_progressBar.Value = 100;

                    //disable timer
                    test_timer.Stop();
                    test_timer.Enabled = false;

                    //update the calibrated variable
                    //cal_panel_x1g.Text = xyzP[0].ToString();

                    //Pass to the next step
                    //calibration_step = 2;
                     
                    */
                    #endregion

                    #endregion

                    cal_panel_x1g.Text = stop_axis_calibration("X +G");
                    

                }
                else if (calibration_step == 2)
                {

                   #region Position Y +1G

                    #region commented
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "Start";
                    cal_panel_label_status.Text = "To calibrate the Y+1G axis, position the wocket as in the picture.\r\n" +
                                                  "When ready, click START.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[2];
                     
                    //Pass to the next step
                    //calibration_step = 3;

                     
                    */
                    #endregion
                   #endregion

                    position_axis_calibration("Y +G", 2);
                  
                }
                else if (calibration_step == 3)
                {
                    
                    #region Start Calibrate Y +1G
                    #region commented
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Y+1G...\r\n" +
                                                  "Keep the wocket in the same position.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //--- set test started = true
                    is_test_finished = false;

                    //--- clean up the mean and std variables

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[2];

                    //--- enable-start calibration timer
                    //--- within the timer call the calibration function
                    ////calibrate wocket
                    */
                    #endregion 
                    #endregion

                    start_axis_calibration("Y +G",false);
                    
                }
                else if (calibration_step == 4)
                {
                    
                    #region Stop Calibrate Y+1G
                    /*
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "Y+1G axis has been calibrated.\r\n" +
                                                  "Click OK to continue...";

                    //pause test
                    is_test_finished = true;

                    //update progres bar 
                    cal_panel_progressBar.Value = 100;
                     
                    //Pass to the next step
                    //calibration_step = 5;

                    */
                    #endregion

                    //update the calibrated variable
                    cal_panel_y1g.Text = stop_axis_calibration("Y +G");

                   
                }
                else if (calibration_step == 5)
                {
                    #region Position X-1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "Start";
                    cal_panel_label_status.Text = "To calibrate the X -1G axis, position the wocket as in the picture.\r\n" +
                                                  "When ready, click START.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[1];
                     
                    //temporal
                    //calibration_step = 6;
                     
                    */
                    #endregion

                    position_axis_calibration("X -G", 1);

                    
                }
                else if (calibration_step == 6)
                {
                    #region Start Calibrate X-1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating X -1G...\r\n" +
                                                  "Keep the wocket in the  same position.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //--- set test started = true
                    is_test_finished = false;

                    //--- clean up the mean and std variables for X-G

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[1];

                    //--- enable-start calibration timer
                    //--- within the timer call the calibration function
                    ////calibrate wocket
                     
                    //temporal
                    calibration_step = 7;
                     
                    */
                    #endregion

                    start_axis_calibration("X -G", false);

              
                }
                else if (calibration_step == 7)
                {
                    #region Stop Calibrate X-1G
                    /*
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "X-1G axis has been calibrated.\r\n" +
                                                  "Click OK to continue...";

                   //pause test
                    is_test_finished = true;

                    //update progres bar 
                    cal_panel_progressBar.Value = 100;
                    
                     //Pass to the next step
                    //calibration_step = 8;
                    
                    */
                    #endregion

                    //update the calibrated variable
                    cal_panel_xn1g.Text = stop_axis_calibration("X -G");

                }
                else if (calibration_step == 8)
                {
                    #region Position Y -1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "Start";
                    cal_panel_label_status.Text = "To calibrate the Y-1G axis, position the wocket as in the picture.\r\n" +
                                                  "When ready, click START.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[3];
                    */
                    #endregion

                    position_axis_calibration("Y -G", 3);

                    //Pass to the next step
                    //calibration_step = 9;
                }
                else if (calibration_step == 9)
                {

                    #region Start Calibrate Y -1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Y-1G...\r\n" +
                                                  "Keep the wocket in the same position.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //--- set test started = true
                    is_test_finished = false;

                    //--- clean up the mean and std variables

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[3];

                    //--- enable-start calibration timer
                    //--- within the timer call the calibration function
                    ////calibrate wocket
                   
                    //temporal
                    calibration_step = 10;
                    
                    */
                    #endregion

                    start_axis_calibration("Y -G", false);

                }
                else if (calibration_step == 10)
                {
                    
                    #region Stop Calibrate Y -1G
                    /*
                    //cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "Y-1G axis has been calibrated.\r\n" +
                                                  "Click OK to continue...";

                   //pause test
                    is_test_finished = true;

                    //update progres bar 
                    cal_panel_progressBar.Value = 100;
                    */
                    #endregion

                   //update the calibrated variable
                    cal_panel_yn1g.Text = stop_axis_calibration("Y -G");

                    //Pass to the next step
                    //calibration_step = 11;
                }
                else if (calibration_step == 11)
                {
                    #region Position Z-1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "Start";
                    cal_panel_label_status.Text = "To calibrate the Z-1G axis, position the wocket as in the picture.\r\n" +
                                                  "When ready, click START.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[5];
                    */
                    #endregion

                    position_axis_calibration("Z -G", 5);

                    //Pass to the next step
                    //calibration_step = 12;
                }
                else if (calibration_step == 12)
                {
                    
                    #region Start Calibrate Z-1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Z-1G...\r\n" +
                                                  "Keep the wocket in the same position.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //--- set test started = true
                    is_test_finished = false;

                    //--- clean up the mean and std variables

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[5];

                    //--- enable-start calibration timer
                    //--- within the timer call the calibration function
                    ////calibrate wocket

                    //temporal
                    calibration_step = 13;
                    */

                    #endregion

                    start_axis_calibration("Z -G", false);

                }
                else if (calibration_step == 13)
                {
                    
                    #region Stop Calibrate Z-1G
                    /*
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "Z-1G axis has been calibrated.\r\n" +
                                                  "Click OK to continue...";

                    //pause test
                    is_test_finished = true;

                    //update progres bar 
                    cal_panel_progressBar.Value = 100;
                    */
                    #endregion

                   
                    //update the calibrated variable
                    cal_panel_zn1g.Text = stop_axis_calibration("Z -G");

                    //Pass to the next step
                    //calibration_step = 14;

                }
                else if (calibration_step == 14)
                {
                    
                    #region Position Z+1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "Start";
                    cal_panel_label_status.Text = "To calibrate the Z+1G axis, position the wocket in the picture.\r\n" +
                                                  "When ready, click START.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[4];
                    */
                    #endregion

                    position_axis_calibration("Z +G", 4);

                    //Pass to the next step
                    //calibration_step = 15;
                }
                else if (calibration_step == 15)
                {

                    #region Start Calibrate Z+1G
                    /*
                    //cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "NEXT";
                    cal_panel_label_status.Text = "Calibrating Z+1G...\r\n" +
                                                  "Keep the wocket in the same position.";

                    //progress bar
                    cal_panel_progressBar.Value = 0;
                    cal_panel_progressBar.Visible = true;

                    //--- set test started = true
                    is_test_finished = false;

                    //--- clean up the mean and std variables

                    //update the image
                    pictureBox_calibration.Image = calibrationImages[4];

                    //--- enable-start calibration timer
                    //--- within the timer call the calibration function
                    ////calibrate wocket
                    
                     * //temporal
                    calibration_step = 16; 
                    
                    */
                    #endregion

                    start_axis_calibration("Z +G", true);

                }
                else if (calibration_step == 16)
                {
                    
                    #region Stop Calibrate Z+1G
                    /*
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "OK";
                    cal_panel_label_status.Text = "Z+1G axis has been calibrated.\r\n" +
                                                  "Click OK to continue...";
                     //pause test
                    is_test_finished = true;

                    //update progres bar 
                    cal_panel_progressBar.Value = 100;
                    */
                    #endregion

                    //update the calibrated variable
                    cal_panel_z1g.Text = stop_axis_calibration("Z +G");

                    //Pass to the next step
                    //calibration_step = 17;

                }
                else if (calibration_step == 17)
                {

                    #region Select File Browser

                    //cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = "Click the Browse button to select the file output folder.\r\n" +
                                                  "Otherwise, the SensorData file will be saved on the desktop.";

                    //show select folder button
                    cal_panel_entry_path.Enabled = true;
                    cal_panel_entry_path.Visible = true;

                    cal_panel_cmd_label.Visible = true;

                    cal_panel_button_browse.Enabled = true;
                    cal_panel_button_browse.Visible = true;

                    //progress bar
                    cal_panel_progressBar.Visible = false;
                    cal_panel_progressBar.Value = 0;

                    //picture box
                    pictureBox_calibration.Visible = false;

                    #endregion 

                    calibration_step = 18;

                }
                else if (calibration_step == 18)
                {
                    
                    #region SAVE values

                    //cal_panel_button_ok.Enabled = false;
                    //cal_panel_button_ok.Text = "SAVE";
                    //cal_panel_label_status.Text = "Saving results to file...";
                    //Application.DoEvents();


                    //Get the current time
                    DateTime timenow = DateTime.Now;

                    //save results
                    string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                                   String.Format("{0:HH:mm:ss}", timenow);

                    //Save values to the test results string
                    TestResults[0] = stime + ",calibration,x+," + xyzP[0].ToString();
                    TestResults[1] = stime + ",calibration,x-," + xyzN[0].ToString();
                    TestResults[2] = stime + ",calibration,xstd," + xyzSTD[0].ToString();
                    TestResults[3] = stime + ",calibration,y+," + xyzP[1].ToString();
                    TestResults[4] = stime + ",calibration,y-," + xyzN[1].ToString();
                    TestResults[5] = stime + ",calibration,ystd," + xyzSTD[1].ToString();
                    TestResults[6] = stime + ",calibration,z+," + xyzP[2].ToString();
                    TestResults[7] = stime + ",calibration,z-," + xyzN[2].ToString();
                    TestResults[8] = stime + ",calibration,zstd," + xyzSTD[2].ToString();


                    //---- Finish the calibration process ------
                    // Determine the axis standard deviations
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();


                    //update the test status
                    info_cmd_value_WKTCalibration.Text = "Calibrated on " + String.Format("{0:HH:mm:ss}", timenow);

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Calibration Test Finished.";

                    #endregion

                    //clean up the steps
                    calibration_step = -1;

                }

                #endregion Calibration


            }
            else if (current_command.CompareTo("battery_calibration") == 0)
            {
                #region Battery Calibration

                //Initialize Battery Calibration test
                if (bat_calibration_step == 0)
                {
                    #region Start Calibration

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Calibrating Battery Values...";
                    cal_panel_bat_values.Visible = true;
                    cal_panel_bat_values_percent.Visible = true;
                    Application.DoEvents();

                    // start battery calibration & initialize time counters
                    is_test_finished = false;
                    BTCAL_OffTime = TimeSpan.Zero;
                    BTCAL_StartTime = DateTime.Now;
                    cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);

                    //Enable Timer
                    test_timer.Enabled = true;
                    test_timer.Start();

                    //Pass to the next step
                    bat_calibration_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The battery test has started.\r\n Click CANCEL if you want to exit the test.";

                    #endregion

                } //Pause/Stop test
                else if (bat_calibration_step == 1)
                {

                    #region STOP Battery CAL test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "START";
                    cal_panel_label_status.Text = " The battery test has PAUSED.\r\n Click START if you want to resume.\r\n Click CANCEL if you want to exit the test.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;
                    BTCAL_StopOffTime = DateTime.Now;

                    //Restart the CAL test
                    bat_calibration_step = 2;
                    cal_panel_button_ok.Enabled = true;

                    #endregion
                }
                //Restart Calibration test
                else if (bat_calibration_step == 2)
                {
                    #region Resume Calibration

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Calibrating Battery Values...";
                    cal_panel_bat_values.Visible = true;
                    Application.DoEvents();

                    // start battery calibration
                    is_test_finished = false;
                    //BTCAL_OffTime = TimeSpan.Zero;
                    //BTCAL_StartTime = DateTime.Now;
                    //cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);
                    BTCAL_OffTime = BTCAL_OffTime.Add(DateTime.Now.Subtract(BTCAL_StopOffTime));


                    //Pass to the next step
                    bat_calibration_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The battery test is RUNNING.\r\n Click CANCEL if you want to exit the test.";

                    #endregion

                }
                else if (bat_calibration_step == 3)
                {

                    #region Finish the Battery CAL test & Show Browse Folder

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = "Please select the folder where you want to save the SensorData.xml file.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;

                    //Pass to the next step
                    bat_calibration_step = 4;
                    cal_panel_button_ok.Enabled = true;

                    #endregion

                }
                else if (bat_calibration_step == 4)
                {

                    #region Save Battery Calibration Values

                    //stop battery calibration
                    is_test_finished = true;
                    DateTime timenow = DateTime.Now;

                    #region Commented
                    ////take the path from the file field
                    //string path = cal_panel_entry_path.Text;
                    //string filename = "SensorData_" + wocket.DeviceAddress.ToString().Substring(7) + ".xml";


                    //if (path.Trim().CompareTo("") == 0)
                    //{
                    //    path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);
                    //}
                    //else if (!Directory.Exists(path))
                    //{
                    //    path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);
                    //}


                    //// Save the calibration values to File
                    //path = path + "\\WocketsConfiguration\\" + filename;

                    ////save_battery_calibration_to_file(wc, path);
                    #endregion

                    //save results
                    string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                                   String.Format("{0:HH:mm:ss}", timenow);

                    //Save values to the test results string
                    TestResults[12] = stime + ",battery_calibration,100%," + bat_cal_values[0].ToString();
                    TestResults[13] = stime + ",battery_calibration,80%," + bat_cal_values[1].ToString();
                    TestResults[14] = stime + ",battery_calibration,60%," + bat_cal_values[2].ToString();
                    TestResults[15] = stime + ",battery_calibration,40%," + bat_cal_values[3].ToString();
                    TestResults[16] = stime + ",battery_calibration,20%," + bat_cal_values[4].ToString();
                    TestResults[17] = stime + ",battery_calibration,10%," + bat_cal_values[5].ToString();


                    //Finish the test
                    bat_calibration_step = -1;
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();

                    //update the test status
                    info_cmd_value_BTCalibration.Text = "Calibrated on " + String.Format("{0:HH:mm:ss}");

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Battery Calibration Test Finished.";



                    #endregion

                }

                #endregion Battery Calibration

            }
            else if (current_command.CompareTo("sampling_rate") == 0)
            {
                #region Sampling Rate Test

                //Initialize Sampling Rate test
                if (sr_test_step == 0)
                {
                    #region Start SR Test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Testing Sampling Rate...\r\n" +
                                                  "Keep the wocket in the SAME POSITION during the test.\r\n" +
                                                  "Click CANCEL if you want to exit.";
                    cal_panel_bat_values.Visible = true;
                    cal_panel_bat_values_percent.Visible = false;
                    //Application.DoEvents();

                    // start battery calibration & initialize time counters
                    is_test_finished = false;
                    BTCAL_OffTime = TimeSpan.Zero;
                    BTCAL_StartTime = DateTime.Now;
                    cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", BTCAL_StartTime);
                    SR = 0;
                    CUMSR = 0;
                    SRCount = 0;

                    //Enable Timer
                    test_timer.Enabled = true;
                    test_timer.Start();

                    //Pass to the next step
                    sr_test_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    //cal_panel_label_status.Text = "The test has started.\r\n" + 
                    //                              "Click CANCEL if you want to exit.";

                    #endregion

                } //Pause/Stop test
                else if (sr_test_step == 1)
                {

                    #region STOP SR test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "RESUME";
                    cal_panel_label_status.Text = "The test has PAUSED.\r\n" + 
                                                  "Click RESUME if you want to continue.\r\n"+
                                                  "Click CANCEL if you want to exit.";
                    //Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;
                    BTCAL_StopOffTime = DateTime.Now;

                    //Restart the CAL test
                    sr_test_step = 2;
                    cal_panel_button_ok.Enabled = true;

                    #endregion
                }
                //Restart Calibration test
                else if (sr_test_step == 2)
                {
                    #region Resume SR Test

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "PAUSE";
                    cal_panel_label_status.Text = "Testing Sampling Rate...";
                    cal_panel_bat_values.Visible = true;
                    cal_panel_bat_values_percent.Visible = false;
                    //Application.DoEvents();

                    // start battery calibration
                    is_test_finished = false;
                    BTCAL_OffTime = BTCAL_OffTime.Add(DateTime.Now.Subtract(BTCAL_StopOffTime));


                    //Pass to the next step
                    sr_test_step = 1;
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_label_status.Text = " The test is RUNNING.\r\n Click CANCEL if you want to exit.";

                    #endregion

                }
                else if (sr_test_step == 3)
                {

                    #region Finish the SR test & Display Save option

                    cal_panel_button_ok.Enabled = false;
                    cal_panel_button_ok.Text = "SAVE";
                    cal_panel_label_status.Text = "The test has FINISHED.\r\n" + 
                                                  "Please click SAVE to exit.";
                    Application.DoEvents();

                    //stop battery calibration
                    is_test_finished = true;

                    //Pass to the next step
                    sr_test_step = 4;
                    cal_panel_button_ok.Enabled = true;

                    #endregion

                }
                else if (sr_test_step == 4)
                {

                    #region Save SR Value

                    //stop the test
                    is_test_finished = true;
                    DateTime timenow = DateTime.Now;

                    #region Commented

                    ////take the path from the file field
                    //string path = cal_panel_entry_path.Text;
                    //string filename = "SensorData_" + wocket.DeviceAddress.ToString().Substring(7) + ".xml";

                    //if (path.Trim().CompareTo("") == 0)
                    //{ path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop); }
                    //else if (!Directory.Exists(path))
                    //{ path = Environment.GetFolderPath(Environment.SpecialFolder.Desktop);}

                    //// Save the calibration values to File
                    //path = path + "\\WocketsConfiguration\\" + filename;

                    //save_sampling_rate_to_file(wc, path);

                    #endregion

                    //save results
                    TestResults[10] = String.Format("{0:MM-dd-yy}", timenow) + " " +
                                      String.Format("{0:HH:mm:ss}", timenow) + ",sampling_rate,SR," +
                                      SR.ToString();

                    //reset parameters
                    sr_test_step = -1;
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();

                    //update the test status
                    info_cmd_value_SRQuality.Text = "Tested on " + String.Format("{0:HH:mm:ss}", timenow);

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Sampling Rate Test Finished.";



                    #endregion

                }

                #endregion Sampling Rate Test

            }
        }


        private void restore_status_panel()
        {
            
            //Disable timer
            test_timer.Enabled = false;
            test_timer.Stop();
                
            StartBTLevel = 0;
            BTCAL_OffTime = TimeSpan.Zero;

            cal_panel_bat_label_startTime.Text = "";
            cal_panel_bat_label_elapTime.Text = "";


            //close battery log file
            if (log_file != null)
            {
               log_file.Flush();
               log_file.Close();
               log_file = null;
            }
            

            //Restore status panel
            panel_status_texbox.Text = "";
            panel_status.Visible = true;

            //clean calibration panel
            cal_panel_title.Text = "";
            cal_panel_cmd_label.Text = "";
            cal_panel_entry_path.Text = "";

            clean_calibration_values(false);

            cal_panel_bat_values.Visible = false;
            cal_panel_cal_values.Visible = false;

            panel_calibration.Visible = false;
            
            //buttons
            button_load.Enabled = true;
            button_finish.Enabled = true;
            button_start_test.Enabled = true;
            button_to_xml.Enabled = true;

            //reset variables
            //is_sensordata_valid = false;
            is_test_finished = true;

            //Close Data Plotter
            plotToolStripMenuItem.Checked = true;
            plotData();

            Application.DoEvents();

            //Stop Reading The Thread
            StopReading();


        }

        private void clean_calibration_values(bool clean_array)
        {

            if (current_command.CompareTo("calibration") == 0)
            {
                //update the calibration fields
                cal_panel_x1g.Text = "";
                cal_panel_xn1g.Text = "";
                cal_panel_xstd.Text = "";

                cal_panel_y1g.Text = "";
                cal_panel_yn1g.Text = "";
                cal_panel_ystd.Text = "";

                cal_panel_z1g.Text = "";
                cal_panel_zn1g.Text = "";
                cal_panel_zstd.Text = "";

                //clean cal values arrays 
                if (clean_array)
                {
                    xyzP[0] = 0.0;
                    xyzP[1] = 0.0;
                    xyzP[2] = 0.0;

                    xyzN[0] = 0.0;
                    xyzN[1] = 0.0;
                    xyzN[2] = 0.0;

                    xyzSTD[0] = 0.0;
                    xyzSTD[1] = 0.0;
                    xyzSTD[2] = 0.0;
                }

            }
            else if (current_command.CompareTo("battery_calibration") == 0)
            { 
                // clean bat cal values on panel
                cal_panel_bat_100.Text = "";
                cal_panel_bat_80.Text = "";
                cal_panel_bat_60.Text = "";
                cal_panel_bat_40.Text = "";
                cal_panel_bat_20.Text = "";
                cal_panel_bat_10.Text = "";
                
                //clean bat cal values arrays
                if (clean_array)
                {
                    for (int i = 0; i < bat_cal_values.Length; i++)
                    {
                        bat_cal_values[i] = 0.0;
                        target_bat_cal_values[i] = 0.0;
                    }
                }

            }

        }

        #endregion 


        #region Save Results Functions

        private bool save_calibration_to_file(WocketsController wc_xml, string fpath)
        {
            bool success = false;

            try
            {
                //Write to the sensordata file
                TextWriter tw = new StreamWriter(fpath);
                tw.WriteLine(wc_xml.ToXML());
                tw.Flush();
                tw.Close();

                //Read from the sensordata file
                WocketsController wc_cal = new WocketsController("", "", "");
                wc_cal.FromXML(fpath);

                Accelerometer acc_sensor = (Accelerometer)wc_cal._Sensors[0];

                //load the fields
                acc_sensor._X1g = xyzP[0];
                acc_sensor._Y1g = xyzP[1];
                acc_sensor._Z1g = xyzP[2];

                acc_sensor._Xn1g = xyzN[0];
                acc_sensor._Yn1g = xyzN[1];
                acc_sensor._Zn1g = xyzN[2];

                acc_sensor._XStd = xyzSTD[0];
                acc_sensor._YStd = xyzSTD[1];
                acc_sensor._ZStd = xyzSTD[2];

                //save to file
                tw = new StreamWriter(fpath);
                tw.WriteLine(wc_cal.ToXML());
                tw.Flush();
                tw.Close();

                success = true;
            }
            catch
            {
                success = false;
            }

            return success;
        }

        private bool save_battery_calibration_to_file(WocketsController wc_xml, string fpath)
        {
            bool success = false;

            try
            {
                //Write to the sensordata file
                TextWriter tw = new StreamWriter(fpath);
                tw.WriteLine(wc_xml.ToXML());
                tw.Flush();
                tw.Close();

                //Read from the sensordata file
                WocketsController wc_cal = new WocketsController("", "", "");
                wc_cal.FromXML(fpath);

                //Save the battery cal values
                //needs to be done

                //save to file
                tw = new StreamWriter(fpath);
                tw.WriteLine(wc_cal.ToXML());
                tw.Flush();
                tw.Close();

                success = true;
            }
            catch
            {
                success = false;
            }

            return success;
        }

      
        private bool save_sampling_rate_to_file(WocketsController wc_xml, string fpath)
        {
            bool success = false;

            try
            {
                //Write to the sensordata file
                TextWriter tw = new StreamWriter(fpath);
                tw.WriteLine(wc_xml.ToXML());
                tw.Flush();
                tw.Close();

                //Read from the sensordata file
                WocketsController wc_cal = new WocketsController("", "", "");
                wc_cal.FromXML(fpath);

                Accelerometer acc_sensor = (Accelerometer)wc_cal._Sensors[0];

                //load the SR field
                acc_sensor._SamplingRate = SR;
               
                //save to file
                tw = new StreamWriter(fpath);
                tw.WriteLine(wc_cal.ToXML());
                tw.Flush();
                tw.Close();

                success = true;
            }
            catch
            {
                success = false;
            }

            return success;
        }


        private bool write_results_to_file(string[] res)
        {
            bool success = false;

            try
            {
                //Create test results file
               string filename = OUTPUT_DIRECTORY +
                                  wocket.DeviceAddress.ToString().Substring(7) + "_" +
                                  "Test_" + String.Format("{0:MMddyy-HHmmss}", DateTime.Now) + ".txt";

                TextWriter testfile = new StreamWriter(filename);

                for (int i = 0; i < res.Length; i++)
                { testfile.WriteLine(res[i]); }

                //close file
                testfile.Flush();
                testfile.Close();

                success = true;
            }
            catch (Exception e)
            { Console.WriteLine(e.ToString());
              success = false;
            }


            return success;

        }


        private bool write_results_to_xml(WocketsController wc_xml)
        {

            bool success = false;

            try
            {
                //Stablish File Path
                string path = cal_panel_entry_path.Text;
                string filename = "SensorData_" + wocket.DeviceAddress.ToString().Substring(7) + ".xml";

                if (path.Trim().CompareTo("") == 0)
                {  path = OUTPUT_DIRECTORY; }
                else if (!Directory.Exists(path))
                {  path = OUTPUT_DIRECTORY; }

                // Save the calibration values to File
                path = path + filename;


                //Write to the sensordata file
                TextWriter tw = new StreamWriter(path);
                tw.WriteLine(wc_xml.ToXML());
                tw.Flush();
                tw.Close();

                //Read from the sensordata file
                WocketsController wc_cal = new WocketsController("", "", "");
                wc_cal.FromXML(path);

                Accelerometer acc_sensor = (Accelerometer)wc_cal._Sensors[0];

                //set the ACC calibration values
                acc_sensor._X1g = xyzP[0];
                acc_sensor._Y1g = xyzP[1];
                acc_sensor._Z1g = xyzP[2];

                acc_sensor._Xn1g = xyzN[0];
                acc_sensor._Yn1g = xyzN[1];
                acc_sensor._Zn1g = xyzN[2];

                acc_sensor._XStd = xyzSTD[0];
                acc_sensor._YStd = xyzSTD[1];
                acc_sensor._ZStd = xyzSTD[2];

                //set the Sampling Rate values
                acc_sensor._SamplingRate = SR;

                //set the battery calibration values
                //set the RSSI values

                //save to file
                tw = new StreamWriter(path);
                tw.WriteLine(wc_cal.ToXML());
                tw.Flush();
                tw.Close();

                success = true;
            }
            catch
            {
                success = false;
            }

            return success;
        }


        #endregion

        
        #region Close Form

            private void Form7_FormClosing(object sender, FormClosingEventArgs e)
            {
                close_form();
            }

            private void button_finish_Click(object sender, EventArgs e)
            {
                close_form();
                this.Close();
            }

            private void close_form()
        {
            if (plotterForm != null)
            {
                plotterForm.Close();
                plotterForm = null;
            }

            //write the test results & Xml to file
            if (!write_results_to_file(TestResults))
            { Console.WriteLine("problem writing to test results file"); }

        }

        #endregion



        #region Commented
        //Wockets Data Reader Extraction
        //private int myHead = 0;
        //private int myTail = 0;
        //private double lastUnixTime = 0.0;
        //private double[] accMeans = new double[3]{0.0, 0.0, 0.0};
        //private int DecodedPackets = 0;
        //Wockets.Utils.CircularBuffer cbuffer;

        //if ( (!is_test_finished) && ( current_command.CompareTo("calibration")== 0) )
            //{}
        #endregion 



    #region Compute Calibration 

    private double[] RMEANS = new double[3]{0.0, 0.0, 0.0};
    private double[] RSTD   = new double[3] { 0.0, 0.0, 0.0 };

    private double lastUnixTime = 0.0;
    private int MaxSamples = 1800;
    private int DecodedPackets = 0;
    private bool is_reading = false;
    //private Wockets.Data.Accelerometers.AccelerationData[] cbuffer;
    private double[,] cbuffer;
    private bool CALIBRATE_STD = false;


    //Thread
    private object _objLock = new object();
    private Thread readingThread = null;

    //Delegate
    //private delegate void updateCalibrationDelegate();
    //public event OnNewCalibrationEventHandler OnNewCalibration;
        
        
   
  

    public void StartReading()
    {
        lock (_objLock)
        {
            if (readingThread != null)
                return;

            readingThread = new Thread(new ThreadStart(ReadingLoop));
            readingThread.Start();
        }
    }


    public void StopReading()
    {
        lock (_objLock)
        {
            if (readingThread == null)
                return;

            is_reading = false;
            readingThread.Join();
            readingThread = null;
        }
    }



    private void ReadingLoop()
    {
        
        //Initialize time stamps 
        double curUnixTime = 0.0;

        //Initialize the means
        double[] accMeans = new double[3] { 0.0, 0.0, 0.0 };

        RMEANS[0] = 0.0;
        RMEANS[1] = 0.0;
        RMEANS[2] = 0.0;

        RSTD[0] = 0.0;
        RSTD[1] = 0.0;
        RSTD[2] = 0.0;

        //Initialize buffer pointers
        int myHead = wc._Decoders[0]._Head;
        int myTail = myHead;
        

        //Initialize the acceleration data 
        DecodedPackets = 0;
        Wockets.Data.Accelerometers.AccelerationData data = ((Wockets.Data.Accelerometers.AccelerationData)wc._Decoders[0]._Data[myHead]);
        
        cbuffer[DecodedPackets,0] = data._X;
        cbuffer[DecodedPackets,1] = data._Y;
        cbuffer[DecodedPackets,2] = data._Z;
        
        myTail++;
        
        

       try
        {
            is_reading = true;

            //Get the data samples
            #region Get Data Samples
           
            while ( (myTail != myHead) && 
                    (data.UnixTimeStamp > 0) &&
                    (DecodedPackets < MaxSamples -1) && 
                    (is_reading))
            {
                //check if the ACC data is valid
                curUnixTime = data.UnixTimeStamp;

                //if (curUnixTime < lastUnixTime)
                //{
                //    MessageBox.Show("Data overwritten without decoding");
                //    break;
                //}


                //update data & time stamps 
                lastUnixTime = curUnixTime;

                accMeans[0] = accMeans[0] + data._X;
                accMeans[1] = accMeans[1] + data._Y;
                accMeans[2] = accMeans[2] + data._Z;

                //update the number of decoded packets
                DecodedPackets++;

                if (DecodedPackets == 1799)
                { }

                //get new data value
                data = ((Wockets.Data.Accelerometers.AccelerationData)wc._Decoders[0]._Data[myTail]);
                
                cbuffer[DecodedPackets,0] = data._X;
                cbuffer[DecodedPackets,1] = data._Y;
                cbuffer[DecodedPackets,2] = data._Z;


                //update the tail
                if (myTail >= wc._Decoders[0]._Data.Length - 1)
                    myTail = 0;
                else
                    myTail++;

            }

            DecodedPackets++;

            //compute the final mean result
            if (DecodedPackets > 1)
            {
                for (int i = 0; i < 3; i++)
                {
                    //compute the mean
                    RMEANS[i] = accMeans[i] / DecodedPackets;

                    if (CALIBRATE_STD)
                    {   //compute the standard deviation
                        for (int j = 0; j < DecodedPackets; j++)
                        {
                            RSTD[i] = RSTD[i] + Math.Pow( cbuffer[j,i] - RMEANS[i], 2.0);
                        }

                        RSTD[i] = Math.Sqrt(RSTD[0] / DecodedPackets);
                    }
                }
            }

            //Finish Test & Update Delegate
            calibration_step = calibration_step + 1;

        }
        catch
        {
            DecodedPackets = -1;
        }
             

        #endregion 


       #region commented
        //commented ----- 
         //temporal code
         //System.Threading.Thread.Sleep(5000);
         //calibration_step = calibration_step + 1;
       // commented -----
       #endregion

       System.Threading.Thread.Sleep(1500);

       //Indicate that the reading loop ended
        is_reading = false;
        is_test_finished = true;
        

    }//function ends


     
    private int compute_calibration_stats(string axis_id, out string st_result)
    {
        int success = -1;
        double result = 0.0;


        if (DecodedPackets >= MaxSamples)
        {
          
            //status: The calibration data was collected successfully;
            success = 0;

            // Assign the mean value to the appropriate axis
            switch (axis_id)
            { 
                case "X +G":
                    xyzP[0] = RMEANS[0];
                    result = xyzP[0];
                    break;
                case "X -G":
                    xyzN[0] = RMEANS[0];
                    result  = xyzN[0];
                    break;
                case "Y +G":
                    xyzP[1] = RMEANS[1];
                    result = xyzP[1];
                    break;
                case "Y -G":
                    xyzN[1] = RMEANS[1];
                    result = xyzN[1];
                    break;
                case "Z +G":
                    xyzP[2] = RMEANS[2];
                    result = xyzP[2];
                    break;
                case "Z -G":
                    xyzN[2] = RMEANS[2];
                    result = xyzN[2];
                    break;
                default:
                    break;

            }

            // Asign the std. dev. 
            if (CALIBRATE_STD)
            {   
                for (int i = 0; i < 3; i++)
                    xyzSTD[i] = RSTD[i];
            }
        }


        st_result = String.Format("{0:0.00}", result);


        return success;
    }


    #endregion 


    }//end class
}//end namespace