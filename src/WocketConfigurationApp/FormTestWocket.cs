using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Threading;

using System.Media;
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
using Wockets.Data.Plotters;


namespace WocketConfigurationApp
{

   
public partial class FormTestWocket : Form
{

  
 #region Declare Variables

        private String wocket_address = "";
        private String wocket_name = "";

        //private delegate void updateTextDelegate_Wocket();
        //private delegate void updateSearchDelegate_Wocket();
        private WocketsController wc;


        //This delegate enables asynchronous calls for setting the text property on a Panel.
        delegate void DelegateUpdateSRPanel(double my_sr, int my_tct, int my_trials, string msg);
        delegate void DelegateUpdatePictureBox(string result);
        
        //---- Commands ---------------
        private string current_command = "";
        private bool IsTestRunning = false;
        private bool IsTestStepFinished = true;


        //----- calibration panel variables  ------------
        private double[] xyzP = new double[3] { 0.0, 0.0, 0.0 };
        private double[] xyzN = new double[3] { 0.0, 0.0, 0.0 };
        private double[] xyzSTD = new double[3] { 0.0, 0.0, 0.0 };

        public static string NEEDED_FILES_PATH = "..\\..\\bin\\NeededFiles\\";
        public static string CALIBRATIONS_DIRECTORY = NEEDED_FILES_PATH + "images\\calibrations\\";
        private Image[] calibrationImages;
        int calibration_step = -1;


        //------ Battery Calibration Variables  -------
        public static string BATTERY_DIRECTORY = NEEDED_FILES_PATH + "images\\battery\\";
        private Image[] bat_calibrationImages;
        
        private DateTime StartTime;
        private DateTime CurTime;

        private DateTime MeasurementLastTime;
        private TimeSpan MeasurementElapsedTime = TimeSpan.Zero;
        
        private TimeSpan OffTime;
        private DateTime StopOffTime;

        private TimeSpan ElapsedTime = TimeSpan.Zero;
        private int SR = 0;

        //100%, 80%, 60%, 40%, 20%, 10%
        private double[] target_bat_cal_values = new double[6] { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 };
        private double[] bat_cal_values = new double[6] { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 };

        private int CAL_UPDATE_SECS = 1000 * 60 * 1; // Sample battery every min
        
        private int StartBTLevel = 0;
        private int CurBTLevel = 0;

        private TextWriter log_file = null;
        private string log_filename = "";

        private TextWriter log_file_battery = null;
        private string log_filename_battery = "";

        private TextWriter log_file_pc = null;
        private string log_filename_pc = "";

        private TextWriter log_file_status = null;
        private string log_filename_status = "";
        
        private string OUTPUT_DIRECTORY = "";

        string[] TestResults = new String[4];


        //------ Threads ------------
        
        


        #endregion


  #region Initialize & Dispose

        //Initialize Class
        public FormTestWocket(String address, String name)
        {
            InitializeComponent();


            //Copy parameters to loacal variables
            this.wocket_address = address;
            this.wocket_name = name;

            //Identify the wocket on the GUI
            this.Text = "Wocket (" + address + ")";
            this.info_cmd_value_name.Text = name;
            this.info_cmd_value_mac.Text = address;

            //clean the test logs on GUI
            this.panel_status_texbox.Text = "";

            //disable test running flag
             IsTestRunning = false;

            //load status panels
            this.panel_status.Visible = true;

            //load calibration panel
            this.panel_calibration.Visible = false;

            //hide battery calibration log text box
            this.cal_panel_battery_log_textBox.Visible = false;
            this.cal_panel_battery_log_textBox.Text = "";


            //calibration images
            this.calibrationImages = new Image[7];

            for (int i = 0; (i < 6); i++)
                this.calibrationImages[i] = (Image)new Bitmap(CALIBRATIONS_DIRECTORY + "calibration" + (i + 1) + ".png");

            //bat calibration images
            this.bat_calibrationImages = new Image[6];

            for (int i = 0; (i < 6); i++)
                this.bat_calibrationImages[i] = (Image)new Bitmap(BATTERY_DIRECTORY + "battery" + (i + 1) + ".png");




            //output directory
            OUTPUT_DIRECTORY = Environment.GetFolderPath(Environment.SpecialFolder.Desktop) +
                               "\\WocketsTest\\";  //Session_" + String.Format("{0:MMddyy-HHmmss}", DateTime.Now) + "\\";

            if (!Directory.Exists(OUTPUT_DIRECTORY))
            { Directory.CreateDirectory(OUTPUT_DIRECTORY); }



           //clean calibration values
            clean_calibration_values("calibration", true);
            clean_calibration_values("battery_calibration", true);
            clean_calibration_values("sampling_rate", true);

            ////Initialize Test Results
            TestResults[0] = "calibration,No Calibrated";
            TestResults[1] = "distance_test,No Tested";
            TestResults[2] = "sampling_rate,No Tested";
            TestResults[3] = "battery_calibration,No Calibrated";

            #region commented
            //TestResults[4] = ",calibration,y-,0.0";
            //TestResults[5] = ",calibration,ystd,0.0";
            //TestResults[6] = ",calibration,z+,0.0";
            //TestResults[7] = ",calibration,z-,0.0";
            //TestResults[8] = ",calibration,zstd,0.0";
            //TestResults[9] = "";
            //TestResults[10] = ",sampling_rate,SR,0";
            //TestResults[11] = "";
            //TestResults[12] = ",battery_calibration,100%,0";
            //TestResults[13] = ",battery_calibration,80%,0";
            //TestResults[14] = ",battery_calibration,60%,0";
            //TestResults[15] = ",battery_calibration,40%,0";
            //TestResults[16] = ",battery_calibration,20%,0";
            //TestResults[17] = ",battery_calibration,10%,0";
            //TestResults[18] = "";
            //TestResults[19] = ",noise,sdx,0.0";
            //TestResults[20] = ",noise,sdy,0.0";
            //TestResults[21] = ",noise,sdz,0.0";
            
            #endregion

            //Test Status Log File
            log_filename_status = OUTPUT_DIRECTORY + wocket_address.Substring(7) + 
                           "_status_log.txt";

            if (!File.Exists(log_filename_status))
            {
                log_file_status = new StreamWriter(log_filename_status);

                for (int i = 0; i < TestResults.Length; i++)
                    log_file_status.WriteLine(TestResults[i]);

                log_file_status.Flush();
                log_file_status.Close();
            }
            else
            {
                TextReader log_file_status_rd = new StreamReader(log_filename_status);

                for (int i = 0; i < TestResults.Length; i++)
                    TestResults[i] = log_file_status_rd.ReadLine();
            }


            //Initialize test status
            info_cmd_value_WKTCalibration.Text = TestResults[0].Split(',')[1]; //"No Calibrated";
            info_cmd_value_distance_test.Text  = TestResults[1].Split(',')[1]; //"No Tested";
            info_cmd_value_SamplingRate.Text   = TestResults[2].Split(',')[1]; //"No Tested";
            info_cmd_value_BatteryTest.Text    = TestResults[3].Split(',')[1]; //"No Calibrated";
            


            //Sampling Rate Log File
            log_filename = OUTPUT_DIRECTORY +
                           wocket_address.Substring(7) + "_" +
                           "log.txt"; 

            log_file = new StreamWriter(log_filename,true);
          
            log_file.WriteLine("--------------------------------");
            log_file.WriteLine("session," + String.Format("{0:MM-dd-yy HH:mm:ss}", DateTime.Now) + ",");


            //create the thread for sampling data 
            //readingThread = new Thread(ReadingLoop);
            //threads.Add(readingThread.ManagedThreadId,readingThread);

            //create the thread for measuring sampling rate
            //samplingRateThread = new Thread(SamplingRateLoop);
            //threads.Add(samplingRateThread.ManagedThreadId, samplingRateThread);


        }


        private void Form2_Load(object sender, EventArgs e)
        {
            //wocket controller object
            InitializeWocket();

            //commands
            //LoadWocketsParameters();

            Thread.Sleep(1000);

            //Panel for Plotter
            startPlottingData();

            current_command = "start_test";



        }


        private void LoadWocketsParameters()
        {
            Command cmd;

            #region commented
            ////-----  Read the commands when the form is loaded  ------------------------
            //cmd = new GET_FV();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_HV();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_PC();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_BT();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_BP();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_BTCAL();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_CAL();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_SEN();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_TM();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_SR();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

            //cmd = new GET_PDT();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);


            //-----------------------------------------------------------------------
            #endregion 


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

            ((RFCOMMReceiver)wc._Receivers[0])._Address = wocket_address; 
            wc._Receivers[0]._ID = 0;
            wc._Decoders[0]._ID = 0;
            wc._Sensors[0]._Receiver = wc._Receivers[0];
            wc._Sensors[0]._Decoder = wc._Decoders[0];
            ((Accelerometer)wc._Sensors[0])._Max = 1024;
            ((Accelerometer)wc._Sensors[0])._Min = 0;
            wc._Sensors[0]._Loaded = true;

            //initialize circular data buffer
            //cbuffer = new Wockets.Data.Accelerometers.AccelerationData[MaxSamples];
            //cbuffer = new double[MaxSamples ,4];
            //SR = new int[Max_SR_Samples];

            //------------ suscriptions --------------
            //battery level
            wc._Decoders[0].Subscribe(ResponseTypes.BL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //sampling rate
            //wc._Decoders[0].Subscribe(ResponseTypes.SR_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //transmission mode
            //wc._Decoders[0].Subscribe(ResponseTypes.TM_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //battery percent
            //wc._Decoders[0].Subscribe(ResponseTypes.BP_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //sensor sensitivity mode
            //wc._Decoders[0].Subscribe(ResponseTypes.SENS_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //calibration mode
            wc._Decoders[0].Subscribe(ResponseTypes.CAL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //packets count
            wc._Decoders[0].Subscribe(ResponseTypes.PC_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //power down timeout
            //wc._Decoders[0].Subscribe(ResponseTypes.PDT_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //battery calibration
            wc._Decoders[0].Subscribe(ResponseTypes.BTCAL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //hardware version
            //wc._Decoders[0].Subscribe(ResponseTypes.HV_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            //firmware version
            //wc._Decoders[0].Subscribe(ResponseTypes.FV_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));

            //TCT
            wc._Decoders[0].Subscribe(ResponseTypes.TCT_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            

            //---- initialize wocket controller -------
            wc.Initialize();
  
        }


   #endregion Initialize


  #region Timer: Recconect & Test       

        private void timerSampling_Tick(object sender, EventArgs e)
        {

            if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Connected)
            {
                #region Connected

                if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Data)
                { this.label_connect_status.Text = "Connected: Data Mode"; }
                else
                { this.label_connect_status.Text = "Connected: Command Mode"; }


                //if necessary, update progress bar here

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



            if (IsTestRunning)
            {

                // ----  move this part within wocket connected check  ----
                #region Update the progress bar

                if ((current_command.Trim().CompareTo("") != 0) &&
                     (!IsTestStepFinished))
                {
                    //update battery progress bar
                    int val = 0;
                    Math.DivRem(cal_panel_progressBar.Value + 10, 100, out val);
                    cal_panel_progressBar.Value = val;

                    //Update Elapsed time
                    ElapsedTime = ((DateTime)DateTime.Now).Subtract(StartTime);
                    ElapsedTime = ElapsedTime.Subtract(OffTime);

                    cal_panel_bat_label_elapTime.Text = ElapsedTime.ToString().Split('.')[0];
                }

                #endregion


                #region Send Battery Level Command (commented)
                //if ((current_command.CompareTo("battery_calibration") == 0) &&
                //         (!IsTestStepFinished))
                //{
                //    #region Send battery level command

                //    //CurTime = DateTime.Now;
                //    //MeasurementElapsedTime = CurTime.Subtract(MeasurementLastTime);

                //    //if (MeasurementElapsedTime.TotalMilliseconds >= CAL_UPDATE_SECS)
                //    //{
                //    //    //update the time variables
                //    //    MeasurementLastTime = CurTime;

                //    //    // send the command
                //    //    GET_BT cmd = new GET_BT();
                //    //    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                //    //}

                //    #endregion
                //}
                //else 
                #endregion 


                #region Send PC Command
                if ((current_command.CompareTo("battery_calibration") == 0) &&
                         (!IsTestStepFinished))
                {


                    CurTime = DateTime.Now;
                    MeasurementElapsedTime = CurTime.Subtract(MeasurementLastTime);

                    if (MeasurementElapsedTime.TotalMilliseconds >= CAL_UPDATE_SECS)
                    {
                        //update the time variables
                        MeasurementLastTime = CurTime;

                        // send the command Packet Count
                        if (is_cmd_pc_on)
                        {
                            GET_PC cmd_pc = new GET_PC();
                            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd_pc._Bytes);
                        }

                        if (is_cmd_bt_level_on)
                        {
                            GET_BT cmd_bt = new GET_BT();
                            ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd_bt._Bytes);
                        }

                        Thread.Sleep(2000);
                    }

                    
                }
                
                #endregion 

                #region update test status
                if ((  (current_command.CompareTo("calibration")    == 0) ||
                       (current_command.CompareTo("distance_test")  == 0) )
                       //||(current_command.CompareTo("sampling_rate") == 0))
                       && (IsTestStepFinished) && (!is_reading))
                {
                    StopReading();
                    cal_panel_button_ok.Enabled = true;
                    process_calibration();
                }
                else if (   ( current_command.CompareTo("sampling_rate") == 0 ) 
                         && (IsTestStepFinished) && (!is_sr_running) )
                {

                    StopSRThread();
                    cal_panel_button_ok.Enabled = true;
                    process_calibration();
                }


                #endregion

                //if (visualizeThread != null)
                //{
                //    if (!is_visualize_running)
                //        StopVisualizeThread();
                //}
            }


        }


  #endregion



  #region Delegates Callbacks & Process Response Functions

        
    private bool is_cmd_pc_on = false;
    private bool is_cmd_bt_level_on = false;
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
                        process_bat_level_response(response);
                    break;
                    //Sampling Rate
                    case ResponseTypes.SR_RSP:
                        //info_cmd_value_SRQuality.Text = ((SR_RSP)response)._Version.ToString();
                        //process_sr_response(response);
                        break;
                    case ResponseTypes.BP_RSP:
                        info_cmd_value_BatteryTest.Text = ((BP_RSP)response)._Percent.ToString() + "%";
                        break;
                    case ResponseTypes.PC_RSP:
                        process_pc_response(response);
                        is_rsp_received = true;
                        break;
                   case ResponseTypes.BTCAL_RSP:
                       info_cmd_value_BatteryTest.Text = ((BTCAL_RSP)response)._CAL100.ToString() + " " + ((BTCAL_RSP)response)._CAL80.ToString() + " " + ((BTCAL_RSP)response)._CAL60.ToString() + " " + ((BTCAL_RSP)response)._CAL40.ToString() + " " + ((BTCAL_RSP)response)._CAL20.ToString() + " " + ((BTCAL_RSP)response)._CAL10.ToString();
                        break;

                   //TCT Response 
                   case ResponseTypes.TCT_RSP:
                        _TCT = ((TCT_RSP)response)._TCT;
                        _REPS = ((TCT_RSP)response)._REPS;
                        _LAST = ((TCT_RSP)response)._LAST;
                        is_rsp_received = true;
                        break;
                  default:
                        break;
                }

                this.Refresh();
            }
        }


        private void process_bat_level_response(Response bt_response)
       { 
               
                #region Write battery level to screen (commented)

                ////Get BatLevel at 100%
                //if( CurBTLevel > StartBTLevel ) 
                //{
                //    StartBTLevel = CurBTLevel;
                //    cal_panel_bat_100.Text = CurBTLevel.ToString();

                //    //Determine the % for the target battery values
                //    bat_cal_values[0] = CurBTLevel; //%100
                //    target_bat_cal_values[0] = CurBTLevel; //%100
                //    target_bat_cal_values[1] = Math.Floor((double)CurBTLevel * 0.80); //%80
                //    target_bat_cal_values[2] = Math.Floor((double)CurBTLevel * 0.60); //%60
                //    target_bat_cal_values[3] = Math.Floor((double)CurBTLevel * 0.40); //%40
                //    target_bat_cal_values[4] = Math.Floor((double)CurBTLevel * 0.20); //%20
                //    target_bat_cal_values[5] = Math.Floor((double)CurBTLevel * 0.10); //%10

                //    //pictureBox_calibration.Image = bat_calibrationImages[0];
                //    pictureBox_calibration.BackColor = Color.Green;
                //}
                ////Get BatLevel at 80%
                //else if (CurBTLevel < target_bat_cal_values[1] )
                //{
                //    bat_cal_values[1] = CurBTLevel;
                //    cal_panel_bat_80.Text = CurBTLevel.ToString();

                //    //pictureBox_calibration.Image = bat_calibrationImages[1];
                //    pictureBox_calibration.BackColor = Color.YellowGreen;
                //}
                ////Get BatLevel at 60%
                //else if (CurBTLevel < target_bat_cal_values[2])
                //{
                //    bat_cal_values[2] = CurBTLevel;
                //    cal_panel_bat_60.Text = CurBTLevel.ToString();

                //    //pictureBox_calibration.Image = bat_calibrationImages[2];
                //    pictureBox_calibration.BackColor = Color.Yellow;
                //}
                ////Get BatLevel at 40%
                //else if (CurBTLevel < target_bat_cal_values[3])
                //{
                //    bat_cal_values[3] = CurBTLevel;
                //    cal_panel_bat_40.Text = CurBTLevel.ToString();

                //    //pictureBox_calibration.Image = bat_calibrationImages[3];
                //    pictureBox_calibration.BackColor = Color.Gold;
                //}
                ////Get BatLevel at 20%
                //else if (CurBTLevel < target_bat_cal_values[4])
                //{
                //    bat_cal_values[4] = CurBTLevel;
                //    cal_panel_bat_20.Text = CurBTLevel.ToString();

                //    //pictureBox_calibration.Image = bat_calibrationImages[4];
                //    pictureBox_calibration.BackColor = Color.Orange;
                //}
                ////Get BatLevel at 10%
                //else if (CurBTLevel < target_bat_cal_values[5])
                //{
                //    bat_cal_values[5] = CurBTLevel;
                //    cal_panel_bat_10.Text = CurBTLevel.ToString();
               
                //    //Finish the test
                //    IsTestStepFinished = true;
                //    calibration_step = 3;
                //    process_calibration();

                //    //pictureBox_calibration.Image = bat_calibrationImages[5];
                //    pictureBox_calibration.BackColor = Color.Red;
                //}

                #endregion 
                #region Map Batt Levels to Interface

                //if (bat_label_index == 0)
                //{
                //    cal_panel_bat_100.Text = CurBTLevel.ToString();
                //    pictureBox_calibration.BackColor = Color.YellowGreen;
                //    bat_label_index++;
                //}
                //else if (bat_label_index == 1)
                //{
                //    cal_panel_bat_80.Text = CurBTLevel.ToString();
                //    pictureBox_calibration.BackColor = Color.Orange;
                //    bat_label_index++;
                //}
                //else if (bat_label_index == 2)
                //{
                //    cal_panel_bat_60.Text = CurBTLevel.ToString();
                //    pictureBox_calibration.BackColor = Color.YellowGreen;
                //    bat_label_index++;
                //}
                //else if (bat_label_index == 3)
                //{
                //    cal_panel_bat_40.Text = CurBTLevel.ToString();
                //    pictureBox_calibration.BackColor = Color.Orange;
                //    bat_label_index++;
                //}
                //else if (bat_label_index == 4)
                //{
                //    cal_panel_bat_20.Text = CurBTLevel.ToString();
                //    pictureBox_calibration.BackColor = Color.YellowGreen;
                //    bat_label_index++;
                //}
                //else 
                //{
                //    cal_panel_bat_10.Text = CurBTLevel.ToString();
                //    pictureBox_calibration.BackColor = Color.Orange;
                //    bat_label_index = 0;
                //}

                #endregion


                //Time stamp the reading
                DateTime timenow = DateTime.Now;
                CurBTLevel = ((BL_RSP)bt_response)._BatteryLevel;

                //Construct the result log
                string result = String.Format(  "{0:MM/dd/yy}", timenow) + " " + 
                                                String.Format("{0:HH:mm:ss}", timenow)   + "," + 
                                                CurBTLevel.ToString() ;


                if (current_command.CompareTo("battery_calibration") == 0)
                {
                    cal_panel_battery_log_textBox.Text = cal_panel_battery_log_textBox.Text + "\r\n" +
                                                         "Battery Level:  " + result;

                    //Write the battery level to file
                    if (log_file_battery != null)
                        log_file_battery.WriteLine(result);
                    
                }
                else
                {
                    //Log the battery level to the panel
                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               "Battery Level:  " + result + "\r\n";
                }                                             
        }


        private void process_pc_response(Response _response)
        {

            //Time stamp the reading
            DateTime timenow = DateTime.Now;
            int CurPC = ((PC_RSP)_response)._Count;
            string result = "";


            if (current_command.CompareTo("battery_calibration") == 0)
            {
                result = String.Format("{0:MM/dd/yy}", timenow) + " " +
                                                String.Format("{0:HH:mm:ss}", timenow) + "," +
                                                CurPC.ToString();

                cal_panel_battery_log_textBox.Text = cal_panel_battery_log_textBox.Text + "\r\n" +
                                                     "Packet Count:  " + result;
                //Write the battery level to file
                if (log_file_pc != null)
                   log_file_pc.WriteLine(result);
           
            }
            else if ( (current_command.CompareTo("sampling_rate") == 0) ||
                      (current_command.CompareTo("distance_test") == 0)   )
            {
                current_packet_count_time = timenow;
                current_packet_count = CurPC;

            }
            else
            {
                result = "Packet Count:  " + String.Format("{0:MM/dd/yy}", timenow) + " " +
                                             String.Format("{0:HH:mm:ss}", timenow) + "," +
                                             CurPC.ToString();

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           result + "\r\n";
            }

        }

        

  #endregion



  #region Plot Raw Signal


        private WocketsScalablePlotter rawdataPlotter;
        private Bitmap backBuffer = null;
        private Panel wPlottingPanel = null;
        private bool isResized = false;



        private void timerPlotter_Tick(object sender, EventArgs e)
        {
            GraphAccelerometerValues();
        }
       

        private void startPlottingData()
        {

          if (CurrentWockets._Controller != null)
          {

                if ( rawdataPlotter == null && this.wPlottingPanel == null )
                {
                    //Create the panel
                    this.wPlottingPanel = new Panel();
                    this.wPlottingPanel.BackColor = Color.White;
                    this.wPlottingPanel.Size = new Size(440, 260);
                    this.wPlottingPanel.Location = new Point(20, 165);
                    this.wPlottingPanel.BorderStyle = BorderStyle.Fixed3D;
                    this.wPlottingPanel.Visible = true;
                    this.wPlottingPanel.Paint += new PaintEventHandler(plotterPanel_Paint);

                    //add panel to the parent container
                    this.panel1.Controls.Add(wPlottingPanel);

                    //Create the plotter
                    rawdataPlotter = new WocketsScalablePlotter(this.wPlottingPanel, CurrentWockets._Controller);

                    //Enable timer
                    timerPlotter.Enabled = true;

                    if (!wPlottingPanel.Visible)
                        wPlottingPanel.Visible = true;
                }
                else
                {

                    if (!wPlottingPanel.Visible)
                    {
                        wPlottingPanel.Visible = true;
                        timerPlotter.Enabled = true;
                    }

                }
            }

        }


        private void stopPlotData()
        {
            
            if (CurrentWockets._Controller != null)
            {
                if (wPlottingPanel.Visible)
                {
                    wPlottingPanel.Visible = false;
                    timerPlotter.Enabled = false;
                }
            }
        }


       private void plotterPanel_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
       {
           if ((this.wPlottingPanel.Visible) && (backBuffer != null))
               e.Graphics.DrawImage(backBuffer, 0, 0);
       }

       private void GraphAccelerometerValues()
       {
           if ( (backBuffer == null ) || (isResized))
           {
               backBuffer = new Bitmap((int)this.wPlottingPanel.Width, (int)this.wPlottingPanel.Height);
               isResized = false;
           }
           using (Graphics g = Graphics.FromImage(backBuffer))
           {
               rawdataPlotter.Draw(g);
               g.Dispose();
           }

       }


       #region commented


       /// <param name="pevent"></param>
       //protected override void OnPaintBackground(PaintEventArgs pevent)
       //{
       //}


       //void panelPlotter_resize(object sender, system.eventargs e)
       //{
       //    this.timerPlotter.Enabled = false;
       //    this.panelPlotter.Width = this.width;
       //    this.panelPlotter.Height = this.height;
       //    aplotter = new wocketsscalableplotter(this.panelPlotter, CurrentWockets._Controller);
       //    isresized = true;
       //    this.timerPlotter.Enabled = true;
       //}
       #endregion commented 


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
                        info_cmd_value_SamplingRate.BackColor = Color.DimGray;
                        info_cmd_value_SamplingRate.ForeColor = Color.White;
                        info_cmd_label_SamplingRate.ForeColor = Color.Orange;
                        break;
                    case "distance_test":
                        current_command = "";
                        info_cmd_value_distance_test.BackColor = Color.DimGray;
                        info_cmd_value_distance_test.ForeColor = Color.White;
                        info_cmd_label_distance_test.ForeColor = Color.Orange;
                        break;
                    case "battery_calibration":
                        current_command = "";
                        info_cmd_value_BatteryTest.BackColor = Color.DimGray;
                        info_cmd_value_BatteryTest.ForeColor = Color.White;
                        info_cmd_label_BatteryTest.ForeColor = Color.Orange;
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
                  info_cmd_value_SamplingRate.BackColor = Color.DimGray;
                  info_cmd_value_SamplingRate.ForeColor = Color.White;
                  info_cmd_label_SamplingRate.ForeColor = Color.Orange;
                  
              //"packet_count":
                  info_cmd_value_distance_test.BackColor = Color.DimGray;
                  info_cmd_value_distance_test.ForeColor = Color.White;
                  info_cmd_label_distance_test.ForeColor = Color.Orange;
                 
                 
             //"battery_calibration":
                  info_cmd_value_BatteryTest.BackColor = Color.DimGray;
                  info_cmd_value_BatteryTest.ForeColor = Color.White;
                  info_cmd_label_BatteryTest.ForeColor = Color.Orange;
             
            //"calibration":
                  info_cmd_value_WKTCalibration.BackColor = Color.DimGray;
                  info_cmd_value_WKTCalibration.ForeColor = Color.White;
                  info_cmd_label_WKTCalibration.ForeColor = Color.Orange;
            
           
                  
        }

        private void enable_all_fields()
        {
            current_command = "all";

          
            //"sampling_rate":
            info_cmd_value_SamplingRate.BackColor = Color.WhiteSmoke;
            info_cmd_value_SamplingRate.ForeColor = Color.Black;
            info_cmd_label_SamplingRate.ForeColor = Color.WhiteSmoke;

            //"packet_count":
            info_cmd_value_distance_test.BackColor = Color.WhiteSmoke;
            info_cmd_value_distance_test.ForeColor = Color.Black;
            info_cmd_label_distance_test.ForeColor = Color.WhiteSmoke;

            
            //"battery_calibration":
            info_cmd_value_BatteryTest.BackColor = Color.WhiteSmoke;
            info_cmd_value_BatteryTest.ForeColor = Color.Black;
            info_cmd_label_BatteryTest.ForeColor = Color.WhiteSmoke;

            //"calibration":
            info_cmd_value_WKTCalibration.BackColor = Color.WhiteSmoke;
            info_cmd_value_WKTCalibration.ForeColor = Color.Black;
            info_cmd_label_WKTCalibration.ForeColor = Color.WhiteSmoke;

            
        }

        private void info_panel_clean_text_fields()
        {
            info_cmd_value_WKTCalibration.Text = "";
            info_cmd_value_distance_test.Text = "";
            
            info_cmd_value_BatteryTest.Text = "";
            info_cmd_value_SamplingRate.Text = "";
        }

        #endregion



   #region Key EVENTS

        private void info_cmd_value_calibration_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_WKTCalibration, info_cmd_value_WKTCalibration, e.KeyCode, "calibration");
        }


        private void info_cmd_value_distance_test_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_distance_test, info_cmd_value_distance_test, e.KeyCode, "distance_test");
        }


        private void info_cmd_value_SamplingRate_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_SamplingRate,info_cmd_value_SamplingRate, e.KeyCode, "sampling_rate");

        }


        private void info_cmd_value_BatteryTest_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_BatteryTest, info_cmd_value_BatteryTest, e.KeyCode, "battery_calibration");
        }

      
        #endregion




   #region Main Buttons

       private void checkBox_LoadAll_CheckedChanged(object sender, EventArgs e)
       {
           if (checkBox_LoadAll.Checked)
           {  
               enable_all_fields();
           }
           else
           {
               
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
                       info_cmd_value_SamplingRate.Text = "";
                       Application.DoEvents();
                       cmd = new GET_SR();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_calibration":
                       info_cmd_value_BatteryTest.Text = "";
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
           start_test();
       }


       private void button_save_to_wocket_Click(object sender, EventArgs e)
       {


           #region --- Prepare the xml file interface  ----

           //highlight the corresponding field "saving to wocket"
           current_command = "save_to_wocket";
           
           //Disable the buttons in main form
           button_finish.Enabled = false;
           button_start_test.Enabled = false;
           button_save_to_wocket.Enabled = false;

           //Hide Calibration Panel Back Button
           cal_panel_button_back.Visible = false;

           //setup the calibration panel parameters
           cal_panel_title.Text        = "Saving to Wocket";
           cal_panel_cmd_label.Text    = "Path";
           cal_panel_entry_path.Text   = "";
           cal_panel_label_status.Text = "Select the XML file that you want to load.\r\n" +
                                         "Press OK to open the file.";
           cal_panel_button_ok.Text    = "OK";


           //Hide picture box
           pictureBox_calibration.Visible = false;
           pictureBox_calibration.SendToBack();

           //Hide the battery log text box
           cal_panel_battery_log_textBox.SendToBack();
           cal_panel_battery_log_textBox.Visible = false;

           //Hide progress bar
           cal_panel_progressBar.Visible = false;
           cal_panel_progressBar.Value = 0;


           //clean panel parameters
           panel_status.Visible = false;
           cal_panel_bat_label_elapTime.Text = "";
           cal_panel_bat_label_startTime.Text = "";


           //Hide Value Panels
           cal_panel_values_BTpercent.Visible = false;
           cal_panel_cal_values.Visible = false;


           //Show select folder fields
           cal_panel_entry_path.Enabled = true;
           cal_panel_entry_path.Visible = true;

           cal_panel_cmd_label.Visible = true;
           cal_panel_cmd_label.Text = "";

           cal_panel_button_browse.Visible = true;
           cal_panel_button_browse.Enabled = true;


           //calibration panel
           panel_calibration.Visible = true;

           //info_cmd_value_BatteryTest.Text = "Calibrating Battery";
           //pictureBox_calibration.Image = null;
           //clean_calibration_values("battery_calibration", false);

           #endregion


           //start saving calibration steps
           calibration_step = 0;
           cal_panel_button_ok.Enabled = true;
           process_calibration();


       }



           
       


       #region commented
       //private void button_to_xml_Click(object sender, EventArgs e)
       //{
       //    button_to_xml.Enabled = false;

       //    if (!write_results_to_xml(wc))
       //    {
       //        Console.WriteLine("Problem when writing to the xml file.");
       //        panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
       //                                   "Problem when writing to the xml file.";
       //    }
       //    else
       //    {
       //        panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
       //                                   DateTime.Now.ToString() + " : " + "The xml file was sucessfully written.";


       //        ////write to the test file
       //        //if (!write_results_to_file(TestResults))
       //        //{
       //        //    Console.WriteLine("Problem when writing to the test file.");
       //        //    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
       //        //                               "Problem when writing to the test file.";
       //        //}
       //        //else
       //        //{
       //        //    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
       //        //                               DateTime.Now.ToString() + " : " + "The test file was sucessfully written.";
       //        //}


       //    }

       //    button_to_xml.Enabled = true;

       //}

       #endregion 

        #endregion



   #region Panel Buttons



       private void cal_panel_button_ok_Click(object sender, EventArgs e)
        {
            process_calibration();
        }


       private void button_back_Click(object sender, EventArgs e)
       {
           if (calibration_step > 0)
              calibration_step = calibration_step - 4;
          

           if (calibration_step <= 0)
           {
               calibration_step = 0;
               position_axis_calibration("X +G", 0);
           }
           else
               process_calibration();

       }


        private void cal_panel_button_cancel_Click(object sender, EventArgs e)
        {
           
            if ( (current_command.CompareTo("calibration") == 0) ||
                (current_command.CompareTo("start_test") == 0))
            {   
                //info_cmd_value_WKTCalibration.Text = "No Calibrated";
                //TestResults[0] = "calibration,No Calibrated";
                info_cmd_value_WKTCalibration.Text = TestResults[0].Split(',')[1]; 
            }
            else if (current_command.CompareTo("distance_test") == 0)
            {  
                //info_cmd_value_distance_test.Text = "No Tested";
                //TestResults[1] = "distance_test,No Tested";

                info_cmd_value_distance_test.Text = TestResults[1].Split(',')[1]; 
            }
            else if (current_command.CompareTo("sampling_rate") == 0)
            { 
                //info_cmd_value_SamplingRate.Text = "No Tested";
                //TestResults[2] = "sampling_rate,No Tested";

                info_cmd_value_SamplingRate.Text = TestResults[2].Split(',')[1]; 

            }
            else if (current_command.CompareTo("battery_calibration") == 0)
            {
                //info_cmd_value_BatteryTest.Text = "No Calibrated";
                //TestResults[3] = "battery_calibration,No Calibrated";

                info_cmd_value_BatteryTest.Text = TestResults[3].Split(',')[1]; 
            }

            //restore status panel
            restore_status_panel();

        }


        private void cal_panel_button_browseFolder_Click(object sender, EventArgs e)
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
                          //Path is correct
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

        private void cal_panel_button_browseFile_Click(object sender, EventArgs e)
        {
            try
            {
                //check the path selected in the textbox
                this.openFileDialog1.Multiselect = false;
                this.openFileDialog1.FileName = "*.xml";



                if (cal_panel_entry_path.Text.Trim().CompareTo("") != 0)
                {
                    if (Directory.Exists(cal_panel_entry_path.Text))
                       this.openFileDialog1.InitialDirectory = cal_panel_entry_path.Text.ToString();
                    
                }



                //check the path selected in the dialog
                DialogResult result = this.openFileDialog1.ShowDialog();


                if (result == DialogResult.OK)
                {
                    string fullPath = this.openFileDialog1.FileName;

                    cal_panel_entry_path.Text = fullPath;


                    if (cal_panel_entry_path.Text.Trim().CompareTo("") == 0)
                      cal_panel_label_status.Text = "Please provide a valid path";
                    else
                    {
                        
                        //if it is a valid sensordata file with calibration values
                        //open the sensordata file and get the calibration values 
                        //fullPath = fullPath + "\\SensorData.xml";
                        if (File.Exists(fullPath))
                        {

                            //Hide File Selection Fields
                            cal_panel_entry_path.Visible = false;
                            cal_panel_button_browse.Visible = false;
                            cal_panel_cmd_label.Visible = false;


                            //Show the log textbox
                            cal_panel_battery_log_textBox.BringToFront();
                            cal_panel_battery_log_textBox.Visible = true;


                            //Update Status
                            cal_panel_label_status.Text = "The XML file is valid. \r\n" +
                                                       "Please check the values to be sent to the wocket.\r\n" +
                                                       "If they are correct, press OK.";


                            WocketsController wc_xml = new WocketsController("", "", "");
                            wc_xml.FromXML(fullPath);
                            Accelerometer acc_sensor = (Accelerometer)wc_xml._Sensors[0];


                            #region load axis calibration parameters
                           
                            // Visuallize the calibration panels
                            //cal_panel_cal_values.Visible = true;
                            //cal_panel_cal_values_positive.Visible = true;
                            //cal_panel_cal_values_negative.Visible = true;
                            //cal_panel_cal_values_std.Visible = true;
                            cal_panel_battery_log_textBox.Visible = true;
                            cal_panel_battery_log_textBox.Text = "The XML contains the following values: \r\n \r\n";

                            //update the calibration fields
                            //cal_panel_x1g.Text = acc_sensor._Calibration._X1G.ToString();
                            //cal_panel_xn1g.Text = acc_sensor._Calibration._XN1G.ToString();
                            //cal_panel_xstd.Text = acc_sensor._XStd.ToString();

                            //cal_panel_y1g.Text = acc_sensor._Calibration._Y1G.ToString();
                            //cal_panel_yn1g.Text = acc_sensor._Calibration._YN1G.ToString();
                            //cal_panel_ystd.Text = acc_sensor._YStd.ToString();

                            //cal_panel_z1g.Text = acc_sensor._Calibration._Z1G.ToString();
                            //cal_panel_zn1g.Text = acc_sensor._Calibration._ZN1G.ToString();
                            //cal_panel_zstd.Text = acc_sensor._ZStd.ToString();

                            cal_panel_battery_log_textBox.Text = cal_panel_battery_log_textBox.Text + 
                                                                   "Axis Calibration: \r\n";

                            cal_panel_battery_log_textBox.Text = cal_panel_battery_log_textBox.Text +
                                                                  " X+1G = " + acc_sensor._Calibration._X1G.ToString()  + " \r\n" +
                                                                  " X-1G = " + acc_sensor._Calibration._XN1G.ToString() + " \r\n" +
                                                                  " Y+1G = " + acc_sensor._Calibration._Y1G.ToString()  + " \r\n" +
                                                                  " Y-1G = " + acc_sensor._Calibration._YN1G.ToString() + " \r\n" +
                                                                  " Z+1G = " + acc_sensor._Calibration._Z1G.ToString()  + " \r\n" +
                                                                  " Z-1G = " + acc_sensor._Calibration._ZN1G.ToString() + " \r\n" +
                                                                  "\r\n" +
                                                                  "         XSTD= " + String.Format("{0:0.00}", acc_sensor._XStd) + " \r\n" +
                                                                  "         YSTD= " + String.Format("{0:0.00}", acc_sensor._YStd) + " \r\n" +
                                                                  "         ZSTD= " + String.Format("{0:0.00}", acc_sensor._ZStd) + " \r\n \r\n";
                                                                

                            //load the fields
                            xyzP[0] = acc_sensor._Calibration._X1G;
                            xyzP[1] = acc_sensor._Calibration._Y1G;
                            xyzP[2] = acc_sensor._Calibration._Z1G;

                            xyzN[0] = acc_sensor._Calibration._XN1G;
                            xyzN[1] = acc_sensor._Calibration._YN1G;
                            xyzN[2] = acc_sensor._Calibration._ZN1G;

                            xyzSTD[0] = acc_sensor._XStd;
                            xyzSTD[1] = acc_sensor._YStd;
                            xyzSTD[2] = acc_sensor._ZStd;

                            //load the sampling rate
                            SR = acc_sensor._SamplingRate;

                            cal_panel_battery_log_textBox.Text = cal_panel_battery_log_textBox.Text +
                                                                 "Sampling Rate: \r\n" +
                                                                 "         SR= " + acc_sensor._SamplingRate + " \r\n";



                            //write the status to screen
                            //is_sensordata_valid = true;

                            #endregion

 
                            //dispose xml wockets controller
                            acc_sensor.Dispose();
                            wc_xml.Dispose();

                        }
                        else
                        {
                            cal_panel_label_status.Text = "The sensordata file is NOT valid. \r\n" +
                                                          "Please try again or click CANCEL to exit the calibration.";
                        }

                    }
                }

            } // end try
            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }


        }



    #endregion 





   #region Process Calibration Functions 
        

        private int time_between_test = 1000;
        private double MAX_STD_VALUE = 3.0;

        

        //---  Calibration Test  ---------
        private void start_axis_calibration(string axis_name, bool compute_std)
        {
            cal_panel_button_ok.Enabled = false;
            cal_panel_button_ok.Text = "OK";
            cal_panel_label_status.Text = "Calibrating " + axis_name + "...\r\n" +
                                          "Keep the wocket in the same position.";

            //Disable the back button
            cal_panel_button_back.Visible = true;
            cal_panel_button_back.Enabled = false;


            //values for panel
            cal_panel_cal_values.Visible = true;

            //elapsed test time panel
            if ( !panel_time_updates.Visible ) 
                panel_time_updates.Visible = true;


            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;

            //pictureBox Calibration
            pictureBox_calibration.Visible = true;


            // start calibration & initialize time counters
            IsTestStepFinished = false;
            OffTime = TimeSpan.Zero;
            StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);


            //Flag that determines if the axis standard deviations need to be computed
            if (compute_std)
                CALIBRATE_STD = true;

            clean_calibration_values("only_std", false);
            clean_calibration_values(axis_name, false);

            //Start Test
            IsTestRunning = true;

            //Start the reading thread for calibration
            StartReading();

            TestNotify("start");
            //notification_result = "start";
            //StartVisualizeThread();


        }

        private string stop_axis_calibration(string axis_name, bool skip_position_step, 
                                             string next_axis_name, int image_number)
        {
            string calibration_result = "";
            string all_calibration_values = "";
            string test_result = "";
            bool is_test_passed = true;
                   

            //--- stop test  ----
            IsTestStepFinished = true;


            //-- stop test ----
            IsTestRunning = false;

            //--- Get the computed variables  ----
            if (compute_calibration_stats(axis_name, out calibration_result) == 0)
            {

                //---  show the std dev results  -----
                if (CALIBRATE_STD)
                {
                    cal_panel_xstd.Text = String.Format("{0:0.0}", xyzSTD[0]);
                    cal_panel_ystd.Text = String.Format("{0:0.0}", xyzSTD[1]);
                    cal_panel_zstd.Text = String.Format("{0:0.0}", xyzSTD[2]);
                }



                //Determine if the test passed based on the STD
                if ((axis_name.Contains("X") && (xyzSTD[0] > MAX_STD_VALUE)) ||
                    (axis_name.Contains("Y") && (xyzSTD[1] > MAX_STD_VALUE)) ||
                    (axis_name.Contains("Z") && (xyzSTD[2] > MAX_STD_VALUE)))
                {
                    is_test_passed = false;
                    test_result = "The axis standard deviation is too high.";
                }


                //Determine if the test passed 
                if ((axis_name.Contains("X +") && (xyzP[0] > 480)) ||
                     (axis_name.Contains("Y +") && (xyzP[1] > 480)) ||
                     (axis_name.Contains("Z +") && (xyzP[2] > 480)) ||
                     (axis_name.Contains("X -") && (xyzN[0] < 550)) ||
                     (axis_name.Contains("Y -") && (xyzN[1] < 550)) ||
                     (axis_name.Contains("Z -") && (xyzN[2] < 550)))
                {
                    is_test_passed = false;
                    test_result = "The axis calibration value is not within an acceptable range.";
                }

                //Show the back button
                cal_panel_button_back.Visible = true;
                cal_panel_button_back.Enabled = true;


                if (is_test_passed)
                {
                    //if calibration stats successful, pass to the next step
                    calibration_step++;

                    //if skip possition_step == true, it will setup the UI for the next calibration possition
                    //if skip possition_step == false, it will save the calibration values
                    if (!skip_position_step)
                    {

                        //add one steo to skip the possition step
                        calibration_step++;

                        cal_panel_button_ok.Enabled = true;
                        cal_panel_button_ok.Text = "OK";
                        cal_panel_label_status.Text = "The calibration process has successfully finished.\r\n" +
                                                      "Click OK if you want to save the data to the XML file.";
                                                      
                       

                        //update progres bar 
                        cal_panel_progressBar.Value = 100;

                        all_calibration_values =     "x+1G," + String.Format("{0:0.0}", xyzP[0]) + "," +
                                                     "x-1G," + String.Format("{0:0.0}", xyzN[0]) + "," +
                                                     "y+1G," + String.Format("{0:0.0}", xyzP[1]) + "," +
                                                     "y-1G," + String.Format("{0:0.0}", xyzN[1]) + "," +
                                                     "z+1G," + String.Format("{0:0.0}", xyzP[2]) + "," +
                                                     "z-1G," + String.Format("{0:0.0}", xyzN[2]) + ",";


                        //---  show the std dev results  -----
                        if (CALIBRATE_STD)
                        {
                            all_calibration_values = all_calibration_values +
                                                     "stdx," + String.Format("{0:0.0}", xyzSTD[0])  + "," +
                                                     "stdy," + String.Format("{0:0.0}", xyzSTD[1])  + "," +
                                                     "stdz," + String.Format("{0:0.0}", xyzSTD[2]);
                        }

                        //save to log file
                        if (log_file != null)
                            log_file.WriteLine("calibration_test," + all_calibration_values);


                        //Get the current time
                        DateTime timenow = DateTime.Now;
                        string stime = String.Format("{0:MM/dd/yy}", timenow) + " " + String.Format("{0:HH:mm:ss}", timenow);

                        //Save status to file
                        TestResults[0] = "calibration," + "Test Passed On: " + stime;
                        write_results_to_status_file();

                        //Update status on panels
                        info_cmd_value_WKTCalibration.Text = "Last Calibrated: " + String.Format("{0:MM/dd/yy  HH:mm:ss}", timenow);

                        panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                                   timenow.ToString() + ": Calibration Test Finished.\r\n" +
                                                   "Results: \r\n" + 
                                                   "x+1G: " + String.Format("{0:0.0}", xyzP[0]) + ", " +
                                                   "x-1G: " + String.Format("{0:0.0}", xyzN[0]) + ", \r\n" +
                                                   "y+1G: " + String.Format("{0:0.0}", xyzP[1]) + ", "     +
                                                   "y-1G: " + String.Format("{0:0.0}", xyzN[1]) + ", \r\n" +
                                                   "z+1G: " + String.Format("{0:0.0}", xyzP[2]) + ","      +
                                                   "z-1G: " + String.Format("{0:0.0}", xyzN[2]) + ", \r\n" +
                                                   "stdx: " + String.Format("{0:0.0}", xyzSTD[0])  + ", "  +
                                                   "stdy: " + String.Format("{0:0.0}", xyzSTD[1])  + ", "  +
                                                   "stdz: " + String.Format("{0:0.0}", xyzSTD[2])  + "\r\n";

                       
                        //Indicate that the test was finished successfully
                        TestNotify("success");
                        //notification_result = "success";
                        //StartVisualizeThread();
                    }
                    else
                    {
                        //go to the calibration position step
                        if (image_number > 0)
                            position_axis_calibration(next_axis_name, image_number);
                    }

                }
                else  //if test not passed
                {
                    //If calibration stats successful, pass to the next step
                    //Perform the calibration again
                    calibration_step--;

                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "Try";

                    
                    cal_panel_label_status.Text = "The test failed.\r\n" +
                                                   test_result + "\r\n" +
                                                  "Check the wocket position and TRY Again";

                    //indicate that the test has finished.
                    TestNotify("failure");
                    //notification_result = "failure";
                    //StartVisualizeThread();
                }

            } //ends reading calibration results


            //reset the compute std. dev. flag
            CALIBRATE_STD = false;


            return calibration_result;

        }

        private void position_axis_calibration(string axis_name, int image_number)
        {
            cal_panel_button_ok.Enabled = true;
            cal_panel_button_ok.Text = "Start";
            cal_panel_label_status.Text = "To start calibrating the "+ axis_name + " axis,\r\n" + 
                                          "place the wocket as shown in the picture.\r\n" +
                                          "When ready, click START.";

            //Show the back button
            if (calibration_step == 0)
            {
                cal_panel_button_back.Visible = false;
                cal_panel_button_back.Enabled = false;
                calibration_step--;
            }
            else
            {
                cal_panel_button_back.Visible = true;
                cal_panel_button_back.Enabled = true;
            }

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


            //clean test notification
            TestNotify("");
           // notification_result = "";
           // StartVisualizeThread();
        }



        //---- Distance Test  -------
        private double sr_tolerance_distance_test = 1.0;
        private double last_tested_distance = 0.0;


        private void start_distance_test(double distance)
        {
            cal_panel_button_ok.Enabled = false;
            cal_panel_button_ok.Text = "Start";
            cal_panel_label_status.Text = "Walk away from wocket until\r\n" +
                                          "you reach " + String.Format("{0:0.0}", distance) + "m distance. \r\n."; 
                                            

            //values for panel calibration
            cal_panel_cal_values.Visible = true;

            //elapsed test time panel
            if (!panel_time_updates.Visible)
                panel_time_updates.Visible = true;
            
            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;

            
            // start calibration & initialize time counters
            IsTestStepFinished = false;
            OffTime = TimeSpan.Zero;
            StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);


            //Flag that determines if the axis standard deviations need to be computed
            CALIBRATE_STD = true;


            //Enable test
           IsTestRunning = true;

            //Start the reading thread for calibration
            StartReading();

            //----  Indicate the distance test has started ------
            TestNotify("start");
            
        }

        private string stop_distance_test(double distance, bool is_saving)
        {
            string calibration_result = "";
            bool is_test_passed = true;
            string test_result = "";

            //--- stop test  ----
            IsTestStepFinished = true;


            //-- disable test  ---
            IsTestRunning = false;



            #region --- Get the computed variables ----
            if (compute_calibration_stats("all", out calibration_result) == 0)
            {

                //---  show the std dev results  -----
                //update text fields
                cal_panel_x1g.Text = String.Format("{0:0.0}", xyzP[0]);
                cal_panel_y1g.Text = String.Format("{0:0.0}", xyzP[1]);
                cal_panel_z1g.Text = String.Format("{0:0.0}", xyzP[2]);


                if (CALIBRATE_STD)
                {
                    cal_panel_xstd.Text = String.Format("{0:0.0}", xyzSTD[0]);
                    cal_panel_ystd.Text = String.Format("{0:0.0}", xyzSTD[1]);
                    cal_panel_zstd.Text = String.Format("{0:0.0}", xyzSTD[2]);

                    calibration_result = calibration_result +
                                        "stdx," + String.Format("{0:0.0}", xyzSTD[0]) + "," +
                                        "stdy,"  + String.Format("{0:0.0}", xyzSTD[1]) + "," +
                                        "stdz,"  +String.Format("{0:0.0}", xyzSTD[2]) ;
                }


             
                //--- Determine if the test passed based on the STD ---
                if (  (xyzSTD[0] > MAX_STD_VALUE) ||
                      (xyzSTD[1] > MAX_STD_VALUE) ||
                      (xyzSTD[2] > MAX_STD_VALUE)    )
                {
                    is_test_passed = false;
                    test_result = "The axis standard deviation is too high.";
                }


                //--- Determine if the test passed based on the SR ---
                if (is_sampling_rate_enabled)
                {
                    cal_panel_sr.Text = String.Format("{0:0.00}", samplingRate);
                    double diff = Math.Abs(target_sampling_rate - samplingRate);

                    if( diff > sr_tolerance_distance_test)
                    {   is_test_passed = false;
                        test_result = "The sampling rate is out of range.";
                    }  
                }

            }
            else
            {
                  is_test_passed = false;
                  test_result = "The accelerometer data was NOT collected successfully.";
            }

            #endregion 


            if (is_test_passed)
            {
                //if data was successfully collected, pass to the next step
                calibration_step++;
                last_tested_distance = distance;



                //save results to log file
                if (log_file != null)
                {
                    log_file.WriteLine( "distance_test," + String.Format("{0:0.0}",distance) + "m,PASSED," + 
                                        "sr," + String.Format("{0:0.00}",samplingRate) + "," +
                                         calibration_result);
                }


                #region -- setup the GUI for the next test ---

                cal_panel_button_ok.Enabled = true;
                cal_panel_label_status.Text = "";


                if (!is_saving)
                {
                    cal_panel_button_ok.Text = "Start";
                    cal_panel_label_status.Text = "The test at " + String.Format("{0:0.0}", distance) + " METERS has successfully finished.\r\n" +
                                                   "Press START to go to the next test.";
                }
                else
                {
                    cal_panel_button_ok.Text = "Save";
                    cal_panel_label_status.Text = cal_panel_label_status.Text +
                                                  "The distance test has successfully finished.";
                }

                //update progres bar 
                cal_panel_progressBar.Value = 100;


                //reset the compute std. dev. flag
                CALIBRATE_STD = false;

                //----  Indicate the distance test has finished  ------
                TestNotify("success");
                //notification_result = "success";
                //StartVisualizeThread();


                #endregion



              

                //process the next step, if it is not the last step
                //process_calibration();


            }//ends if test passed
            else
            {

                //if test not passed, perform the calibration again
                calibration_step --;

                #region --- setup the GUI for the next test ---

                cal_panel_button_ok.Enabled = true;
                cal_panel_button_ok.Text = "Try Again";

                cal_panel_label_status.Text = "The test has finished.\r\n" +
                                               test_result + "\r\n" +
                                              "Click TRY AGAIN, to repeat the test.";



                //----  Indicate the distance test has finished  ------
                TestNotify("failure");
                //notification_result = "failure";
                //StartVisualizeThread();


                //reset the compute std. dev. flag
                CALIBRATE_STD = false;


                #endregion 

            }


           


            return calibration_result;

        }

        
        //---- Sampling Rate Test -----
        private void start_SamplingRate_test()
        {
            
            cal_panel_button_ok.Enabled = false;
            cal_panel_label_status.Text = "Running Sampling Rate Test...\r\n" +
                                          "Keep the wocket in the SAME POSITION.\r\n" +
                                          "Click CANCEL if you want to exit.";

            //values for panel calibration
            cal_panel_cal_values.Visible = true;
            //cal_panel_cal_values_positive.Visible = false;
            //cal_panel_cal_values_negative.Visible = false;
            //cal_panel_cal_values_std.Visible = false;

            cal_panel_sr_values.Visible = true;
            //cal_panel_sr.Visible = true;
            //cal_panel_tct.Visible = true;
            //cal_panel_trials.Visible = true;

            samplingRate = 0;
            cal_panel_sr.Text = "";
            cal_panel_tct.Text = "";
            cal_panel_trials.Text = "";

            //elapsed test time panel
            if (!panel_time_updates.Visible)
                panel_time_updates.Visible = true;


            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;


            //Start calibration & initialize time counters
           OffTime = TimeSpan.Zero;
            StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);


            //Flag that determines if the axis standard deviations need to be computed
            CALIBRATE_STD = false;


            //Enable test
            IsTestStepFinished = false;
            IsTestRunning = true;

           
           //Start the sampling rate thread
           StartSRThread();

        }

        private void stop_SamplingRate_test()
        {
           

            //--- stop test  ----
            IsTestStepFinished = true;

            //-- disable test ---
            IsTestRunning = false;

            //--- Check Test Results ----
            //Get the current time
            DateTime timenow = DateTime.Now;
            string stime = String.Format("{0:MM/dd/yy}", timenow) + " " +
                           String.Format("{0:HH:mm:ss}", timenow);


            double diff = Math.Abs(target_sampling_rate - samplingRate);

            if( diff < sr_tolerance )
            {
                //if data was successfully collected, pass to the next step
                calibration_step++;
                
                //save to log file
                if (log_file != null)
                {
                    log_file.WriteLine(stime + ",sampling_rate_test,"+ "passed" +
                                        ",target," + String.Format("{0:0.00}", target_sampling_rate) +
                                        ",sr," + String.Format("{0:0.00}",samplingRate) +
                                        ",tct," + _TCT.ToString() + 
                                        ",trials," + _SR_TRIALS.ToString());
                }


                //write the status to calibration panel
                cal_panel_label_status.Text = "The sampling rate test successfully finished. \r\n" +
                                              "Verify the sampling rate. Click OK to save to the xml file.";

                cal_panel_button_ok.Enabled = true;
                cal_panel_button_ok.Text = "OK";



                //Update the global sampling rate variable
                SR = (int)Math.Round(samplingRate);
                

                //update progres bar 
                cal_panel_progressBar.Value = 100;
                
                //update the status info
                info_cmd_value_SamplingRate.Text = "Test Passed On: " + stime;

                TestResults[2] = "sampling_rate," + "Last Test Passed On: " + stime;
                write_results_to_status_file();

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           stime + " : Sampling Rate Test Passed. \r\n" +
                                           "Results : Target= " + String.Format("{0:0.00}",target_sampling_rate) + 
                                           " ,SR= " + String.Format("{0:0.00}", samplingRate) + " ,TCT= " + _TCT.ToString() + " ,TRIALS= " + _SR_TRIALS.ToString() + "\r\n";

                //Notify that test was successful
                //TestNotify("success");
                notification_result = "success";
                StartVisualizeThread();
            }
            else
            {
                //perform the calibration again
                calibration_step--;

                cal_panel_button_ok.Enabled = true;
                cal_panel_button_ok.Text = "Try Again";

                cal_panel_label_status.Text = "The test has finished.\r\n" +
                                              "The DATA WAS NOT collected successfully.\r\n" +
                                              "Click TRY AGAIN, to repeat the test.";


               //save to log file
                if (log_file != null)
                {
                    log_file.WriteLine(stime + ",sampling_rate_test,"+ "failed" +
                                        ",target," + String.Format("{0:0.00}", target_sampling_rate) +
                                        ",sr," + String.Format("{0:0.00}", samplingRate) +
                                        ",tct," + _TCT.ToString() + 
                                        ",trials," + _SR_TRIALS.ToString());
                }



                //Update the global sampling rate variable
                SR = 0;


                //update progres bar 
                cal_panel_progressBar.Value = 0;

                //update the status info
                info_cmd_value_SamplingRate.Text = "No Tested.";

                TestResults[2] = "sampling_rate," + "Test Failed: " + stime;
                write_results_to_status_file();

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           stime + ": Sampling Rate Test Failed. \r\n"  +
                                            "Results : Target= " + String.Format("{0:0.00}", target_sampling_rate) + 
                                           " ,SR= " + String.Format("{0:0.00}", samplingRate) + " TCT= " + _TCT.ToString() + " TRIALS= " + _SR_TRIALS.ToString() + "\r\n";

                //Notify that test was successful
                //TestNotify("failure");
                notification_result = "failure";
                StartVisualizeThread();

            }


           


        }


   #endregion




   #region Process test steps

        //---- Start Test --------
        private void start_test()
        {
            

            if (!checkBox_LoadAll.Checked)
            {

                button_start_test.Enabled = false;
               

                if ((current_command.CompareTo("calibration") == 0) ||
                    (current_command.CompareTo("start_test") == 0))
                {


                    #region Calibration
                   // MaxSamples = 500;
                   // sampling_data_sleep_time_ms = 500;

                    MaxSamples = 1000;
                    sampling_data_sleep_time_ms = 100;
                    is_sampling_rate_enabled = false;


                    #region setup GUI components

                    //highlight the corresponding field
                    change_status_field(info_cmd_label_WKTCalibration, info_cmd_value_WKTCalibration, Keys.Enter, "calibration");

                    //setup the calibration panel parameters
                    cal_panel_title.Text = info_cmd_label_WKTCalibration.Text;
                    //cal_panel_cmd_label.Text = "Path";
                    //cal_panel_entry_path.Text = "";
                    cal_panel_label_status.Text = "Position the wocket as shown in the picture.\r\n" +
                                                  "Then, click START to begin the calibration.\r\n" +
                                                  "During the test, keep the wocket in the same position.";

                    //Panel Buttons
                    cal_panel_button_ok.Text = "Start";

                    //Hide the back button
                    cal_panel_button_back.Text = "Back";
                    cal_panel_button_back.Visible = false;

                    //battery calibration panel
                    cal_panel_values_BTpercent.Visible = false;

                    //elapsed test time panel
                    panel_time_updates.Visible = false;

                    //calibration panel
                    cal_panel_cal_values.Visible = false;
                    cal_panel_cal_values_positive.Visible = true;

                    cal_panel_cal_values_negative.Visible = true;
                    cal_panel_cal_values_negative.Location = new Point(14, 27);

                    cal_panel_cal_values_std.Visible = true;
                    cal_panel_cal_values_std.Location = new Point(14, 54);

                    cal_panel_sr_values.Visible = false;
                    cal_panel_sr_values.SendToBack();


                    //progress bar
                    cal_panel_progressBar.Visible = false;


                    //buttons
                    button_load.Enabled = false;
                    button_finish.Enabled = false;


                    //overall calibration panel
                    panel_calibration.Visible = true;


                    //Hide the battery log textbox
                    cal_panel_battery_log_textBox.SendToBack();
                    cal_panel_battery_log_textBox.Visible = false;

                    //picture box
                    pictureBox_calibration.BringToFront();
                    pictureBox_calibration.Visible = true;
                    pictureBox_calibration.Image = calibrationImages[0];
                    

                   
                    //Hide select folder fields
                    cal_panel_entry_path.Enabled = false;
                    cal_panel_entry_path.Visible = false;

                    cal_panel_cmd_label.Visible = false;

                    cal_panel_button_browse.Enabled = true;
                    cal_panel_button_browse.Visible = false;


                    //clean panel parameters
                    panel_status.Visible = false;
                    cal_panel_bat_label_elapTime.Text = "";
                    cal_panel_bat_label_startTime.Text = "";
                    
                    
                    #endregion


                    //start calibration steps
                    calibration_step = 0;
                    cal_panel_button_ok.Enabled = true;
                    info_cmd_value_WKTCalibration.Text = "Calibrating ...";
                    clean_calibration_values("calibration", false);

                    #endregion Calibration


                }
                else if (current_command.CompareTo("distance_test") == 0)
                {


                    #region Distance Test

                    MaxSamples = 10000;
                    sampling_data_sleep_time_ms = 100;
                    is_sampling_rate_enabled = true;


                    #region --- setup the test GUI ---
                    //highlight the corresponding field
                    change_status_field(info_cmd_label_distance_test, info_cmd_value_distance_test, Keys.Enter, "distance_test");


                    //setup the calibration panel parameters
                    cal_panel_title.Text = info_cmd_label_distance_test.Text;


                    cal_panel_label_status.Text = "Place the wocket on a surface with NO MOVEMENT or VIBRATION. \r\n" +
                                                  "Then, walk away from it after you hear the beep. \r\n" + 
                                                  "Stop when you reach the distance indicated on the screen.\r\n" +
                                                  "Click START when ready.\r\n";


                    cal_panel_button_ok.Text = "Start";

                  

                    //progress bar
                    cal_panel_progressBar.Visible = true;
                    cal_panel_progressBar.Value = 0;


                    //Hide the battery log textbox
                    cal_panel_battery_log_textBox.SendToBack();
                    cal_panel_battery_log_textBox.Visible = false;


                    //picture box
                    pictureBox_calibration.BringToFront();
                    pictureBox_calibration.Visible = true;
                    pictureBox_calibration.Image = calibrationImages[4];


                    //clean panel parameters
                    panel_status.Visible = false;
                    cal_panel_bat_label_elapTime.Text = "";
                    cal_panel_bat_label_startTime.Text = "";

                    //Hide battery Panel
                    cal_panel_values_BTpercent.Visible = false;

                    //Hide the back button
                    cal_panel_button_back.Visible = false;


                    //elapsed test time panel
                    panel_time_updates.Visible = false;


                    //set calibration panel
                    cal_panel_cal_values.Visible = false;
                    cal_panel_cal_values_positive.Visible = true;

                    cal_panel_cal_values_negative.Visible = false;

                    cal_panel_cal_values_std.Visible = true;
                    cal_panel_cal_values_std.Location = new Point(14, 27);

                    cal_panel_sr_values.Visible = true;
                    cal_panel_sr_values.Location = new Point(14, 54);


                    //Hide select folder fields
                    cal_panel_entry_path.Enabled = false;
                    cal_panel_entry_path.Visible = false;
                    cal_panel_cmd_label.Visible = false;
                    cal_panel_button_browse.Enabled = false;
                    cal_panel_button_browse.Visible = false;


                    //--- calibration panel  ---
                    panel_calibration.Visible = true;


                    #endregion 


                    //initialize test steps
                    calibration_step = 0;
                    cal_panel_button_ok.Enabled = true;
                    info_cmd_value_distance_test.Text = "Testing...";

                    //clean fields
                    clean_calibration_values("distance_test", false);


                    #endregion Distance Test

                }
                else if (current_command.CompareTo("sampling_rate") == 0)
                {

                    #region Sampling Rate Test

                    //highlight the corresponding field
                    change_status_field(info_cmd_label_SamplingRate, info_cmd_value_SamplingRate, Keys.Enter, "sampling_rate");


                    //setup the calibration panel parameters
                    cal_panel_title.Text = info_cmd_label_SamplingRate.Text;

                    cal_panel_label_status.Text = "Place the wocket in a surface with NO MOVEMENT \r\n" +
                                                  "or VIBRATION as shown in the picture.\r\n" +
                                                  "When ready, click START.";

                    cal_panel_button_ok.Text = "Start";

                    //Hide Back Button
                    cal_panel_button_back.Visible = false;
                    
                    //progress bar
                    cal_panel_progressBar.Visible = true;
                    cal_panel_progressBar.Value = 0;


                    //Hide the battery log textbox
                    cal_panel_battery_log_textBox.SendToBack();
                    cal_panel_battery_log_textBox.Visible = false;

                    //picture box
                    pictureBox_calibration.BringToFront();
                    pictureBox_calibration.Image = calibrationImages[4];
                    pictureBox_calibration.Visible = true;

                    //clean panel parameters
                    panel_status.Visible = false;
                    cal_panel_bat_label_elapTime.Text = "";
                    cal_panel_bat_label_startTime.Text = "";

                    //battery value Panel
                    cal_panel_values_BTpercent.Visible = false;


                    //set calibration panel
                    cal_panel_cal_values.Visible = false;
                    cal_panel_cal_values_positive.Visible = false;
                    cal_panel_cal_values_negative.Visible = false;
                    cal_panel_cal_values_std.Visible = false;
                    cal_panel_sr_values.Visible = false;
                    
                    cal_panel_sr.Visible = true;
                    cal_panel_tct.Visible = true;
                    cal_panel_trials.Visible = true;

                    //Hide select folder fields
                    cal_panel_entry_path.Enabled = false;
                    cal_panel_entry_path.Visible = false;
                    cal_panel_cmd_label.Visible = false;
                    cal_panel_button_browse.Enabled = false;
                    cal_panel_button_browse.Visible = false;


                    //calibration panel
                    panel_calibration.Visible = true;

                   

                    //initialize test steps
                    calibration_step = 0;
                    cal_panel_button_ok.Enabled = true;
                    info_cmd_value_SamplingRate.Text = "Testing Sampling Rate...";
                    clean_calibration_values("sampling_rate", false);


                    #endregion Sampling Rate Test



                }
                else if (current_command.CompareTo("battery_calibration") == 0)
                {


                    #region Battery Calibration
                    is_sampling_rate_enabled = false;

                    //highlight the corresponding field
                    change_status_field(info_cmd_label_BatteryTest, info_cmd_value_BatteryTest, Keys.Enter, "battery_calibration");

                    //setup the calibration panel parameters
                    cal_panel_title.Text = info_cmd_label_BatteryTest.Text;
                    //cal_panel_cmd_label.Text = "Path";
                    //cal_panel_entry_path.Text = "";
                    cal_panel_label_status.Text = "Make sure that the battery is fully charged.\r\n" +
                                                  "Press START to begin the battery calibration.";

                    cal_panel_button_ok.Text = "Start";



                    //--- Battery Log File  ---
                    //disable send the battery level command
                    is_cmd_bt_level_on = false;

                    log_filename_battery = OUTPUT_DIRECTORY + wocket_address.Substring(7) + "_" + "bat_log.txt";

                    
                    if (!File.Exists(log_filename_battery))
                        log_file_battery = new StreamWriter(log_filename_battery);
                    else
                    {  if (log_file_battery == null)
                            log_file_battery = new StreamWriter(log_filename_battery, true);
                    }


                    //enable send the pc command
                    is_cmd_pc_on = true;

                    log_filename_pc = OUTPUT_DIRECTORY + wocket_address.Substring(7) + "_" + "pc_log.txt";

                    if (!File.Exists(log_filename_pc))
                        log_file_pc = new StreamWriter(log_filename_pc);
                    else
                    {   if (log_file_pc== null)
                           log_file_pc = new StreamWriter(log_filename_pc, true);
                    }


                    // Initialize Battery Current Time
                    MeasurementLastTime = DateTime.Now;

                    //Hide picture box
                    pictureBox_calibration.Visible = false;
                    pictureBox_calibration.SendToBack();

                    //Show Battery log text box
                    cal_panel_battery_log_textBox.BringToFront();
                    cal_panel_battery_log_textBox.Visible = true;
                    
                    //Hide the calibration percent labels
                    

                    //progress bar
                    cal_panel_progressBar.Visible = true;
                    cal_panel_progressBar.Value = 0;


                    //clean panel parameters
                    panel_status.Visible = false;
                    cal_panel_bat_label_elapTime.Text = "";
                    cal_panel_bat_label_startTime.Text = "";


                    //Hide Value Panels
                    cal_panel_values_BTpercent.Visible = false;
                    cal_panel_cal_values.Visible = false;

                    //Hide select folder fields
                    cal_panel_entry_path.Enabled = false;
                    cal_panel_entry_path.Visible = false;
                    cal_panel_cmd_label.Visible = false;
                    cal_panel_button_browse.Visible = false;
                    cal_panel_button_browse.Enabled = false;

                    //calibration panel
                    panel_calibration.Visible = true;
                    //is_sensordata_valid = false;

                    //start battery calibration steps
                    calibration_step = 0;
                    cal_panel_button_ok.Enabled = true;
                    info_cmd_value_BatteryTest.Text = "Calibrating Battery";
                    pictureBox_calibration.Image = null;

                    clean_calibration_values("battery_calibration", false);

                    process_calibration();

                    #endregion BAT Calibration
                }


                else
                {
                    button_start_test.Enabled = true;
                }

            }
        }


        //--- Process a specific test ----
        private void process_calibration()
        {
            if( (current_command.CompareTo("calibration") == 0) ||
                (current_command.CompareTo("start_test") == 0))
            {
                current_command = "calibration";
                process_axis_calibration_step(calibration_step);

            }
            else if (current_command.CompareTo("distance_test") == 0)
            {
                process_distance_test_step(calibration_step);
              
            }
            else if (current_command.CompareTo("sampling_rate") == 0)
            {
                process_sampling_rate_step(calibration_step);

            }
            else if (current_command.CompareTo("battery_calibration") == 0)
            {
                process_battery_calibrate(calibration_step);
            }
            else if (current_command.CompareTo("save_to_wocket") == 0)
            {
                process_save_to_wocket(calibration_step);
            }

        }


        private void process_axis_calibration_step(int step_number )
        {

            #region Wocket Calibration



                if (step_number == 0)
                {
                    clean_calibration_values("calibration", true);
                    start_axis_calibration("X +G", true);

                }
                else if (step_number == 1)
                {
                    cal_panel_x1g.Text = stop_axis_calibration("X +G", true, "Y +G", 2);
                }
                else if (step_number == 2)
                {
                    position_axis_calibration("Y +G", 2);
                }
                else if (step_number == 3)
                {
                    start_axis_calibration("Y +G", true);
                }
                else if (step_number == 4)
                {
                    cal_panel_y1g.Text = stop_axis_calibration("Y +G", true, "X -G", 1);
                }
                else if (step_number == 5)
                {
                    position_axis_calibration("X -G", 1);

                }
                else if (step_number == 6)
                {
                    start_axis_calibration("X -G", true);

                }
                else if (step_number == 7)
                {
                   cal_panel_xn1g.Text = stop_axis_calibration("X -G", true, "Y -G", 3);

                }
                else if (step_number == 8)
                {
                    position_axis_calibration("Y -G", 3);

                }
                else if (step_number == 9)
                {
                    start_axis_calibration("Y -G", true);

                }
                else if (step_number == 10)
                {
                    cal_panel_yn1g.Text = stop_axis_calibration("Y -G", true, "Z -G", 5);
                }
                else if (step_number == 11)
                {
                    position_axis_calibration("Z -G", 5);
                }
                else if (step_number == 12)
                {
                    start_axis_calibration("Z -G", true);
                }
                else if (step_number == 13)
                {
                    cal_panel_zn1g.Text = stop_axis_calibration("Z -G", true, "Z +G", 4);

                }
                else if (step_number == 14)
                {
                    position_axis_calibration("Z +G", 4);
                }
                else if (step_number == 15)
                {
                    start_axis_calibration("Z +G", true);
                }
                else if (step_number == 16)
                {
                    cal_panel_z1g.Text = stop_axis_calibration("Z +G", false, "", 0);

                }
                //step 17 corresponding to possition step needs to be skiped
                else if( step_number == 18)
                {
         
                    //---- Finish the calibration process ------
                    //save the values to XML
                    save_calibration_to_file(wc);

                    //clean status messages
                    cal_panel_label_status.Text = "";

                    //Close calibration panel 
                    restore_status_panel();

                    //clean up the steps
                    calibration_step = -1;

                    //pass to the next test
                    current_command = "distance_test";
                    start_test();

            }

            #endregion Calibration
        
        }

     
        private void process_distance_test_step(int step_number) 
        {


            #region Distance Test

            if (step_number == 0)
            {
                clean_calibration_values("distance_test", true);
                last_tested_distance = 0.0;

                start_distance_test(1.0);

            }
            else if (step_number == 1)
            {
                stop_distance_test(1.0, false);
            }
            else if (step_number == 2)
            {
                
                start_distance_test(5.0);
            }
            else if (step_number == 3)
            {
                stop_distance_test(5.0,false);
            }
            else if (step_number == 4)
            {
                start_distance_test(10.0);
            }
            else if (step_number == 5)
            {
                stop_distance_test(10.0, false);
            }
            else if (step_number == 6)
            {
                start_distance_test(15.0);
            }
            else if (step_number == 7)
            {
                stop_distance_test(15.0, true);
            }
            else if (step_number == 8)
            {
               calibration_step++;
            }
            else if (step_number == 9)
            {
               
               #region save results to log file
               
               //Get the current time
               DateTime timenow = DateTime.Now;
               string stime = String.Format("{0:MM/dd/yy}", timenow) + " " +
                              String.Format("{0:HH:mm:ss}", timenow);


                //update the test status
                info_cmd_value_distance_test.Text = "Last Tested: " + stime;
                TestResults[1] = "distance_test," + "test passed at " + String.Format("{0:0.0}", last_tested_distance) + "m distance on: " + stime;
                write_results_to_status_file();

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           stime + ": distance test PASSED at " + 
                                           String.Format("{0:0.0}", last_tested_distance) + "m distance. \r\n";


               #endregion 


               #region commented
                //Progress To The Next Test
                //Application.DoEvents();
                //Thread.Sleep(time_between_test);
                #endregion


                //--- Finish the test  -------
                cal_panel_label_status.Text = "";

                //Close calibration panel 
                restore_status_panel();

                //clean up the steps
                calibration_step = -1;

                //--- pass to the next test  ----
                current_command = "sampling_rate";
                start_test();

            }

            #endregion Distance Test
        
        }

        private void process_sampling_rate_step(int step_number)
        {

            #region Sampling Rate Test

            //Initialize Sampling Rate test
            if (step_number == 0)
            {
                clean_calibration_values("sampling_rate", true);
                start_SamplingRate_test();

            } //Pause-Stop test
            else if (step_number == 1)
            {
                stop_SamplingRate_test();

                //Pass to the next test
                //process_calibration();

            }
            //Restart Calibration test
            else if (step_number == 2)
            {
                
                //-- Save Results To File
                save_sampling_rate_to_file(wc);
              

                //--- Finish the test  -------
                cal_panel_label_status.Text = "";

                //Close calibration panel 
                restore_status_panel();

                //clean up the steps
                calibration_step = -1;


                //--- pass to the next test -----
                //current_command = "battery_calibration";
                //start_test();
            }


            #endregion Sampling Rate Test

        }

        private void process_battery_calibrate(int step_number)
        {
            #region Battery Calibration

            //Initialize Battery Calibration test
            if (step_number == 0)
            {

                clean_calibration_values("battery_calibration", true);
                
                //elapsed test time panel
                if (!panel_time_updates.Visible)
                    panel_time_updates.Visible = true;


                #region Start Calibration

                cal_panel_button_ok.Enabled = false;
                cal_panel_button_ok.Text = "PAUSE";
                cal_panel_label_status.Text = "Calibrating Battery Values...";
                //cal_panel_values_BTpercent.Visible = true;
                Application.DoEvents();

                // start battery calibration & initialize time counters
                IsTestStepFinished = false;
                OffTime = TimeSpan.Zero;
                StartTime = DateTime.Now;
                cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);

                //Enable Test
                IsTestRunning = true;

                #region commented
                //DateTime timenow = DateTime.Now;
                //string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                //               String.Format("{0:HH:mm:ss}", timenow);

                //TestResults[3] = current_command + "," + "Calibration Started: " + stime;

                //Pass to the next step
                //step_number = 1;
                #endregion 


                calibration_step = 1;

                cal_panel_button_ok.Enabled = true;
                cal_panel_label_status.Text = " The battery test has started.\r\n Click CANCEL if you want to exit the test.";



                #endregion

            } //Pause/Stop test
            else if (step_number == 1)
            {

                #region STOP Battery CAL test

                cal_panel_button_ok.Enabled = false;
                cal_panel_button_ok.Text = "START";
                cal_panel_label_status.Text = " The battery test has PAUSED.\r\n Click START if you want to resume.\r\n Click CANCEL if you want to exit the test.";
                Application.DoEvents();

                //stop battery calibration
                IsTestStepFinished = true;
                StopOffTime = DateTime.Now;

                
                //Restart the CAL test
                //step_number = 2;
                calibration_step = 2;
                
                cal_panel_button_ok.Enabled = true;

                #endregion
            }
            //Restart Calibration test
            else if (step_number == 2)
            {
                #region Resume Calibration

                cal_panel_button_ok.Enabled = false;
                cal_panel_button_ok.Text = "PAUSE";
                cal_panel_label_status.Text = "Calibrating Battery Values...";
                //cal_panel_values_BTpercent.Visible = true;
                Application.DoEvents();

                // start battery calibration
                IsTestStepFinished = false;
                //OffTime = TimeSpan.Zero;
                //StartTime = DateTime.Now;
                //cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);
                OffTime = OffTime.Add(DateTime.Now.Subtract(StopOffTime));


                //Pass to the next step
                //step_number = 1;
                calibration_step = 1;
                
                cal_panel_button_ok.Enabled = true;
                cal_panel_label_status.Text = " The battery test is RUNNING.\r\n Click CANCEL if you want to exit the test.";

                #endregion

            }
            else if (step_number == 3)
            {

                #region Finish the Battery CAL test & Show Browse Folder

                cal_panel_button_ok.Enabled = false;
                cal_panel_button_ok.Text = "SAVE";
                cal_panel_label_status.Text = "Please select the folder where you want to save the SensorData.xml file.";
                Application.DoEvents();

                //stop battery calibration
                IsTestStepFinished = true;

                //Pass to the next step
                //step_number = 4;
                calibration_step = 4;
                
                cal_panel_button_ok.Enabled = true;

                #endregion

            }
            else if (step_number == 4)
            {

                #region Save Battery Calibration Values

                //stop battery calibration
                IsTestStepFinished = true;
                

                # region Save values to the test results string (commented)
                //TestResults[12] = stime + ",battery_calibration,100%," + bat_cal_values[0].ToString();
                //TestResults[13] = stime + ",battery_calibration,80%," + bat_cal_values[1].ToString();
                //TestResults[14] = stime + ",battery_calibration,60%," + bat_cal_values[2].ToString();
                //TestResults[15] = stime + ",battery_calibration,40%," + bat_cal_values[3].ToString();
                //TestResults[16] = stime + ",battery_calibration,20%," + bat_cal_values[4].ToString();
                //TestResults[17] = stime + ",battery_calibration,10%," + bat_cal_values[5].ToString();
                #endregion


                //Finish the test
                //step_number = -1;
                calibration_step = -1;

                cal_panel_label_status.Text = "";

                //Close calibration panel 
                restore_status_panel();

                DateTime timenow = DateTime.Now;
                string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                               String.Format("{0:HH:mm:ss}", timenow);


                //update the test status
                info_cmd_value_BatteryTest.Text = "Last Calibrated: " + stime;

                TestResults[3] = "battery_calibration," + "Last Calibrated: " + stime;
                write_results_to_status_file();

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           timenow.ToString() + ": Battery Calibration Test Finished.";



                #endregion

            }

            #endregion Battery Calibration

        }


        private void process_save_to_wocket(int step_number)
        {

            #region SAVE to wocket code

            //Initialize Sampling Rate test
            if (step_number == 1)
            {
               
               

            } //Pause-Stop test
            else if (step_number == 1)
            {
                
            }
            //Restart Calibration test
            else if (step_number == 2)
            {

                //-- Save Results To File
                save_sampling_rate_to_file(wc);


                //--- Finish the test  -------
                cal_panel_label_status.Text = "";

                //Close calibration panel 
                restore_status_panel();

                //clean up the steps
                calibration_step = -1;


                //--- exit the test -----
                current_command = "";
                
            }


            #endregion 



        }
       
   #endregion 





   #region Panels Clean and Restore


        private void restore_status_panel()
        {
            
            //Disable timer
            IsTestRunning = false;

            //disable the PC/BT commands
            is_cmd_bt_level_on = false;
            is_cmd_pc_on = false;


            //Stop the threads
            //if (current_command.CompareTo("sampling_rate") == 0)
            StopSRThread();
            //else
            StopReading();
            StopVisualizeThread();


            StartBTLevel = 0;
            OffTime = TimeSpan.Zero;

            cal_panel_bat_label_startTime.Text = "";
            cal_panel_bat_label_elapTime.Text = "";

            #region commented
            ////close log file
            //if (log_file != null)
            //{
            //   log_file.Flush();
            //   log_file.Close();
            //   log_file = null;
            //}
            #endregion commented


            //Restore status panel
            panel_status.Visible = true;

            //clean calibration panel
            cal_panel_title.Text = "";
            cal_panel_cmd_label.Text = "";
            cal_panel_entry_path.Text = "";

            cal_panel_values_BTpercent.Visible = false;
            cal_panel_cal_values.Visible = false;

            panel_calibration.Visible = false;


            cal_panel_battery_log_textBox.Visible = false;

            //Disable the buttons in main form
            button_load.Enabled = true;
            button_finish.Enabled = true;
            button_start_test.Enabled = true;
            button_save_to_wocket.Enabled = true;
            //button_to_xml.Enabled = true;


            //reset variables
            IsTestStepFinished = true;
            calibration_step = -1;


            disable_all_fields();
            TestNotify("");
            Application.DoEvents();


           




        }

        
   #endregion


   #region  Calibration Functions

        private int compute_calibration_stats(string axis_id, out string st_result)
        {
            int success = -1;
            st_result = "";


            //if (DecodedPackets >= MaxSamples)
            if (DecodedPackets > 0)
            {

                //status: The calibration data was collected successfully;
                success = 0;

                // Assign the mean value to the appropriate axis
                switch (axis_id)
                {
                    case "X +G":
                        xyzP[0] = RMEANS[0];
                        st_result = String.Format("{0:0.00} ", xyzP[0]);
                        break;
                    case "X -G":
                        xyzN[0] = Convert.ToUInt16(RMEANS[0]);
                        st_result = String.Format("{0:0.00} ", xyzN[0]);
                        break;
                    case "Y +G":
                        xyzP[1] = Convert.ToUInt16(RMEANS[1]);
                        st_result = String.Format("{0:0.00} ", xyzP[1]);
                        break;
                    case "Y -G":
                        xyzN[1] = Convert.ToUInt16(RMEANS[1]);
                        st_result = String.Format("{0:0.00} ", xyzN[1]);
                        break;
                    case "Z +G":
                        xyzP[2] = Convert.ToUInt16(RMEANS[2]);
                        st_result = String.Format("{0:0.00} ", xyzP[2]);
                        break;
                    case "Z -G":
                        xyzN[2] = Convert.ToUInt16(RMEANS[2]);
                        st_result = String.Format("{0:0.00} ", xyzN[2]);
                        break;
                    case "all":
                        xyzP[0] = Convert.ToUInt16(RMEANS[0]);
                        xyzP[1] = Convert.ToUInt16(RMEANS[1]);
                        xyzP[2] = Convert.ToUInt16(RMEANS[2]);


                        st_result = "x," + String.Format("{0:0}", xyzP[0]) + "," +
                                    "y," + String.Format("{0:0}", xyzP[1]) + "," +
                                    "z," + String.Format("{0:0}", xyzP[2]) + ",";
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



            return success;

        }

        private void clean_calibration_values(string cmd_name, bool clean_array)
        {

            if (cmd_name.CompareTo("battery_calibration") == 0)
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
            else
            {

                if (cmd_name.CompareTo("only_std") == 0)
                {
                    cal_panel_xstd.Text = "";
                    cal_panel_ystd.Text = "";
                    cal_panel_zstd.Text = "";
                }
                else if (cmd_name.CompareTo("X +G") == 0)
                {
                    cal_panel_x1g.Text = "";
                    xyzP[0] = 0.0;
                }
                else if (cmd_name.CompareTo("X -G") == 0)
                {
                    cal_panel_xn1g.Text = "";
                    xyzN[0] = 0.0;
                }
                else if (cmd_name.CompareTo("Y +G") == 0)
                {
                    cal_panel_y1g.Text = "";
                    xyzP[1] = 0.0;
                }
                else if (cmd_name.CompareTo("Y -G") == 0)
                {
                    cal_panel_yn1g.Text = "";
                    xyzN[1] = 0.0;
                }
                else if (cmd_name.CompareTo("Z +G") == 0)
                {
                    cal_panel_z1g.Text = "";
                    xyzP[2] = 0.0;
                }
                else if (cmd_name.CompareTo("Z -G") == 0)
                {
                    cal_panel_zn1g.Text = "";
                    xyzN[2] = 0.0;
                }
                else if (cmd_name.CompareTo("sampling_rate") == 0)
                {
                    cal_panel_sr.Text = "";
                    cal_panel_tct.Text = "";
                    cal_panel_trials.Text = "";

                    if (clean_array)
                    {
                        SR = 0;
                        _TCT = 0;
                        _SR_TRIALS = 0;
                    }
                }
                else //clean all  //if (cmd_name.CompareTo("calibration") == 0)
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

                    cal_panel_sr.Text = "";
                    cal_panel_tct.Text = "";
                    cal_panel_trials.Text = "";


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

                        SR = 0;
                        _TCT = 0;
                        _SR_TRIALS = 0;

                    }
                }
            }



        }

  #endregion


   
   #region Compute Calibration

    private double[] RMEANS = new double[3]{0.0, 0.0, 0.0};
    private double[] RSTD   = new double[3] { 0.0, 0.0, 0.0 };

    //sampling rate
    private double samplingRate = 0.0;
    //private long SR_TotalSamples = 0;
    //private DateTime calTime;
   

   //calibration parameters
    private int MaxSamples = 1000;
    private int DecodedPackets = 0;
    private int sampling_data_sleep_time_ms = 500;

    private bool is_sampling_rate_enabled = true;

    //private double[,] cbuffer;
    private bool CALIBRATE_STD = false;

    //Thread
    private object _objLock = new object();
    private Thread readingThread = null;
    private bool is_reading = false;
       

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
            //readingThread.Join();
            readingThread = null;
        }
    }


    private void ReadingLoop()
    {
        //Enable the reading flag
        is_reading = true;


        // Initialize the means
        double[] accMeans = new double[3] { 0.0, 0.0, 0.0 };
        RMEANS[0] = 0.0;
        RMEANS[1] = 0.0;
        RMEANS[2] = 0.0;
        RSTD[0] = 0.0;
        RSTD[1] = 0.0;
        RSTD[2] = 0.0;

        //Initialize bufffer to compute STD
        double[,] cbuffer = new double[MaxSamples, 4];


        // Initialize counter
        DecodedPackets = 0;

        //Initialize Sampling Rate Variables
        current_packet_count = 0;
        DateTime sr_start_time = DateTime.Now; 
        DateTime sr_end_time;
        int start_pc = 0;
        int end_pc = 0;
        


        // Initialize buffer pointers
        // The wockets controller doesn't keep track of the tail
        // it needs to be initialized to the head
        int myHead = wc._Decoders[0]._Head;
        int myTail = myHead;
        Wockets.Data.Accelerometers.AccelerationData data;


        try
        {
            if (is_sampling_rate_enabled ) 
            {
               
                #region Start Measuring the Sampling Rate

                //--- Start measurament: get the start packet count ---
                samplingRate = 0.0;
                is_rsp_received = false;
                GET_PC cmd = new GET_PC();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

                while (!is_rsp_received)
                { Thread.Sleep(500); }
                Thread.Sleep(500);

                sr_start_time = current_packet_count_time;
                start_pc = current_packet_count;

                #endregion 

            }


            #region Get Data Samples

            //-- Loop until the desired number of samples ---
            while ((DecodedPackets < MaxSamples) &&
                    (is_reading))
            {


                //wait and update the head, when the tail has reached the head 
                if (myTail == myHead)
                {
                    System.Threading.Thread.Sleep(sampling_data_sleep_time_ms);
                    myHead = wc._Decoders[0]._Head;
                    continue;
                }


                //get data
                data = ((Wockets.Data.Accelerometers.AccelerationData)wc._Decoders[0]._Data[myTail]);



                //check that the unix time stam
                if (data.UnixTimeStamp > 0.0)
                {
                    //add data values to counters
                    accMeans[0] = accMeans[0] + data._X;
                    accMeans[1] = accMeans[1] + data._Y;
                    accMeans[2] = accMeans[2] + data._Z;

                    if (CALIBRATE_STD)
                    { //add data to buffer
                        cbuffer[DecodedPackets, 0] = data._X;
                        cbuffer[DecodedPackets, 1] = data._Y;
                        cbuffer[DecodedPackets, 2] = data._Z;
                        cbuffer[DecodedPackets, 3] = data.UnixTimeStamp;
                    }

                    //update the number of decoded packets
                    DecodedPackets++;
                }


                //update the tail
                if (myTail >= wc._Decoders[0]._Data.Length - 1)
                    myTail = 0;
                else
                    myTail++;

            }//ends while

            #endregion



            #region compute the final mean result

            if (DecodedPackets > 1)
            {
                //compute the mean
                for (int i = 0; i < 3; i++)
                    RMEANS[i] = accMeans[i] / DecodedPackets;
                


                if (CALIBRATE_STD)
                {   
                    //compute the standard deviation
                    for (int k = 0; k < 3; k++)
                    {
                        for (int j = 0; j < DecodedPackets; j++)
                            RSTD[k] = RSTD[k] + Math.Pow(cbuffer[j, k] - RMEANS[k], 2.0);
                        RSTD[k] = Math.Sqrt(RSTD[k] / DecodedPackets);
                    }
                }
            }

            #endregion 


            
            
            if (is_sampling_rate_enabled)
            {

                #region stop measuring the sampling rate
              
                //-- End measurement: get the final packet count -----
                is_rsp_received = false;
                GET_PC cmd = new GET_PC();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

                while (!is_rsp_received)
                { Thread.Sleep(500); }
                Thread.Sleep(500);

                sr_end_time = current_packet_count_time;
                end_pc = current_packet_count;


                //--- Compute the measured sampling rate  ---
                samplingRate = (end_pc - start_pc) / (((TimeSpan)sr_end_time.Subtract(sr_start_time)).TotalSeconds);

                #endregion
            }

            


            //Finish Test & Update Delegate
            calibration_step = calibration_step + 1;


        }//ends try
        catch
        {
            DecodedPackets = -1;
        }
             
 
       //Indicate that the reading loop ended
        is_reading = false;
        IsTestStepFinished = true;
        

    }//function ends

    
    #endregion 



    #region Check/Fix Sampling Rate

    //Thread
    private object objLock_sr = new object();
    private Thread samplingRateThread = null;
    private bool is_sr_running = false;
    private bool is_rsp_received = false;

    //Sampling Rate Adjustment Settings
    private double target_sampling_rate = 40.0;
    private double sr_tolerance = 0.1;
    private int MAX_SR_TRIALS = 5;
    private int SR_Sampling_Time = 1000 * 60 * 3;
    
    //Global Counters    
    private DateTime current_packet_count_time;
    private int current_packet_count = 0;

    private int _SR_TRIALS = 0;
    private int _TCT = 0;
    private int _REPS = 0;
    private int _LAST = 0;



    public void StartSRThread()
    {
        lock (objLock_sr)
        {
            if (samplingRateThread != null)
                return;

            if (!is_sr_running)
            {
                samplingRateThread = new Thread(new ThreadStart(SamplingRateLoop));
                samplingRateThread.Start();
            }
        }
    }


    public void StopSRThread()
    {
        lock (objLock_sr)
        {

            if (samplingRateThread == null)
                return;

            is_sr_running = false;
            samplingRateThread.Join();
            samplingRateThread = null;
        }
    }


    private void SamplingRateLoop()
    {
        //indicate that the thread has started
        is_sr_running = true;


        //initialize loop
        int _tct = 0;
        bool is_tct_started = false;
        DateTime sr_start_time, sr_end_time;
        int start_pc = 0;
        int end_pc   = 0;
        
        double sr_diff = 0.0;
        double previous_sr_diff = 100.0;
        double previous_sampling_rate = 0.0;
        int previous_tct = 0;
        
       

        //initialize global variables
        current_packet_count = 0;        
        _TCT = 0;
        _REPS = 0;
        _LAST = 0;
        _SR_TRIALS = 0;

        
        //Initialize The Text in SR Panel
        Update_Form_SR(-1, -1, -1, "Sampling ...");


        //loop that checks the SR measurement max. 5 times and corrects it if necessary
        while (_SR_TRIALS < MAX_SR_TRIALS)
        {

            try
            {
                if (!is_tct_started)
                {
                    is_tct_started = true;
                    

                    //-- Start Sampling Rate Measurement -----
                    #region Measure Sampling Rate
                    
                    //--- Start measurament: get the start packet count ---
                    samplingRate = 0.0;
                    is_rsp_received = false;
                    GET_PC cmd = new GET_PC();
                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

                    while (!is_rsp_received)
                    { Thread.Sleep(500); }
                    Thread.Sleep(500);


                    sr_start_time = current_packet_count_time;
                    start_pc = current_packet_count;


                    //--Wait for the SR measurement to be completed --
                    Thread.Sleep(SR_Sampling_Time);


                    //-- End measurement: get the final packet count -----
                    is_rsp_received = false;
                    cmd = new GET_PC();
                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

                    while (!is_rsp_received)
                    { Thread.Sleep(500); }
                    Thread.Sleep(500);

                    sr_end_time = current_packet_count_time;
                    end_pc = current_packet_count;

                    
                    //--- Compute the measured sampling rate  ---
                    samplingRate = (end_pc - start_pc) / ( ((TimeSpan)sr_end_time.Subtract(sr_start_time)).TotalSeconds);

                    #endregion 


                    //--- Compare the response to the target sampling rate  ---
                    sr_diff = target_sampling_rate - ((double)samplingRate);


                    #region Get the current _TCT
                    
                    is_rsp_received = false;

                    //Send Command to get the timer settings
                    GET_TCT cmd_tct = new GET_TCT();
                    ((RFCOMMReceiver)wc._Receivers[0]).Write(cmd_tct._Bytes);

                    //Wait for response
                    while (!is_rsp_received)
                    { Thread.Sleep(500); }
                    Thread.Sleep(500);
                    
                    #endregion


                    //--- Check that the sampling rate diff is indeed reduced ---
                    if (sr_diff < previous_sr_diff)
                    {
                        #region Check if the Sampling Rate Diff is within the tolerance

                        if (Math.Abs(sr_diff) < sr_tolerance)
                        {
                            //do nothing, the sampling rate is acceptable
                            Update_Form_SR(samplingRate, _TCT, _SR_TRIALS + 1, "The sampling rate is similar to the target.");
                            break;
                        }
                        else
                        {
                            Update_Form_SR(samplingRate, _TCT, _SR_TRIALS + 1, "The Sampling Rate needs to be corrected.");

                            #region Fix the TCT

                            if (_TCT != 0)
                            {

                                Update_Form_SR(samplingRate, _TCT, _SR_TRIALS + 1, "The TCT was received.");
                                _tct = _TCT;
                                

                                // if SR is higher than the target, decrease TCT
                                // if SR is lower than the target, increase TCT
                                if (sr_diff < 0)
                                    _tct--;
                                else
                                    _tct++;


                                // Write the new TCT value to the wocket
                                // Be carefull to not excesively write cmds to the wocket
                                // the EPPROM has a limited number of write cycles
                                SET_TCT setcmd = new SET_TCT(_tct, _REPS, _LAST);
                                ((RFCOMMReceiver)wc._Receivers[0]).Write(setcmd._Bytes);

                                //Wait for the command be transmitted
                                Thread.Sleep(4000);


                                Update_Form_SR(samplingRate, _TCT, _SR_TRIALS + 1, "The corrected TCT = " + _tct.ToString() + " was sent.");


                                #region Confirm that the command was set properly (commented)
                                //is_rsp_received = false;
                                //_TCT = 0;

                                //////Send Command to get the timer settings
                                //cmd = new GET_TCT();
                                //((RFCOMMReceiver)wc._Receivers[0]).Write(cmd._Bytes);

                                //////Wait for response
                                //while (!is_rsp_received)
                                //{ Thread.Sleep(500); }

                                //Thread.Sleep(300);


                                //////check if the tct value corresponds to the one we modified
                                ////if (_TCT == _tct)
                                ////{  //set tct cmd was successful }
                                ////else
                                ////{ //tct cmd not set}
                                #endregion


                            }//if SR_TCT good ends


                            #endregion

                        }//else sr_diff ends

                        #endregion


                        //Update values
                        previous_sampling_rate = samplingRate;
                        previous_sr_diff = sr_diff;
                        previous_tct = _TCT;
                    }
                    else
                    { 
                        //Set the TCT to the previous value
                        // Be carefull to not excesively write cmds to the wocket
                        // the EPPROM has a limited number of write cycles
                        SET_TCT setcmd = new SET_TCT(previous_tct, _REPS, _LAST);
                        ((RFCOMMReceiver)wc._Receivers[0]).Write(setcmd._Bytes);

                        //Wait for the command be transmitted
                        Thread.Sleep(4000);


                        //the sampling rate is in the global minimum
                        Update_Form_SR(previous_sampling_rate, previous_tct, _SR_TRIALS + 1, 
                                       "The sampling rate reached its global minimum. \r\n TCT= " + previous_tct.ToString());
                        break;
                    }

                    //after the TCT command was set to the new value, try to measure the SR again
                    _SR_TRIALS++;
                    is_tct_started = false;

                }// if tct started


            }//try ends
            catch
            {   //if the operation failed, try to measure the SR again
                _SR_TRIALS++;
            }

        }//while ends


        //Indicate that the loop ended
        calibration_step++;
        IsTestStepFinished = true;
        is_sr_running = false;



    }//function ends




    #endregion 

  
   
   
    #region Save Results To File Functions

    private bool save_calibration_to_file(WocketsController wc_xml)
    {
        bool success = false;

        try
        {

            //Stablish File Path
            string fpath = OUTPUT_DIRECTORY; //cal_panel_entry_path.Text;
            string filename = wocket_address.Substring(7) + "_SensorData.xml";
            fpath = fpath + filename;

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
            acc_sensor._Calibration._X1G = (ushort) xyzP[0];
            acc_sensor._Calibration._Y1G = (ushort)xyzP[1];
            acc_sensor._Calibration._Z1G = (ushort)xyzP[2];

            acc_sensor._Calibration._XN1G = (ushort)xyzN[0];
            acc_sensor._Calibration._YN1G = (ushort)xyzN[1];
            acc_sensor._Calibration._ZN1G = (ushort)xyzN[2];

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

    private bool save_sampling_rate_to_file(WocketsController wc_xml)
    {
        bool success = false;

        try
        {
            //Stablish File Path
            string fpath = OUTPUT_DIRECTORY; //cal_panel_entry_path.Text;
            string filename = wocket_address.Substring(7) + "_SensorData.xml";

            //if (path.Trim().CompareTo("") == 0)
            //{ path = OUTPUT_DIRECTORY; }
            //else if (!Directory.Exists(path))
            //{ path = OUTPUT_DIRECTORY; }

            // Save the calibration values to File
            fpath = fpath + filename;


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


    private void finish_save_to_string(string cmd_name)
    {
        //Get the current time
        DateTime timenow = DateTime.Now;
        string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                       String.Format("{0:HH:mm:ss}", timenow);



        
        if (cmd_name.CompareTo("distance_test") == 0)
        {
            #region test results (commented)
            ////TestResults[10] = stime + ",sampling_rate,sr," + "";
            //TestResults[19] = stime + ",noise,xstd," + xyzSTD[0].ToString();
            //TestResults[20] = stime + ",noise,ystd," + xyzSTD[1].ToString();
            //TestResults[21] = stime + ",noise,zstd," + xyzSTD[2].ToString();
            #endregion


            //update the test status
            info_cmd_value_distance_test.Text = "Last Tested: " + stime; 
            TestResults[1] = "distance_test," + "Last Tested: " + stime;
            write_results_to_status_file();

            panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                      stime + ": Distance Test Finished.";


        }
        else if (cmd_name.CompareTo("sampling_rate") == 0)
        {
            #region commented
            ////TestResults[10] = stime + ",sampling_rate,sr," + "";
            //TestResults[19] = stime + ",noise,xstd," + xyzSTD[0].ToString();
            //TestResults[20] = stime + ",noise,ystd," + xyzSTD[1].ToString();
            //TestResults[21] = stime + ",noise,zstd," + xyzSTD[2].ToString();
            #endregion 

            //update the test status
            info_cmd_value_SamplingRate.Text = "Last Tested: " + stime; 
            TestResults[2] = "sampling_rate,"+ "Last Tested: " + stime;
            write_results_to_status_file();

            panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                       stime+ ": Sampling Rate Test Finished.";
        }

        //---- Finish the calibration process ------
        // Determine the axis standard deviations
        cal_panel_label_status.Text = "";

        //Close calibration panel 
        restore_status_panel();

        //clean up the steps
        calibration_step = -1;

    }


    private bool write_results_to_file(string[] res)
    {
        bool success = false;

        try
        {
            //Create test results file
            string filename = OUTPUT_DIRECTORY +
                               wocket_address.Substring(7) + "_" +
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
        {
            Console.WriteLine(e.ToString());
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
            string filename = wocket_address.Substring(7) + "_SensorData.xml";

            if (path.Trim().CompareTo("") == 0)
            { path = OUTPUT_DIRECTORY; }
            else if (!Directory.Exists(path))
            { path = OUTPUT_DIRECTORY; }

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
            acc_sensor._Calibration._X1G = (ushort)xyzP[0];
            acc_sensor._Calibration._Y1G = (ushort)xyzP[1];
            acc_sensor._Calibration._Z1G = (ushort)xyzP[2];

            acc_sensor._Calibration._XN1G = (ushort)xyzN[0];
            acc_sensor._Calibration._YN1G = (ushort)xyzN[1];
            acc_sensor._Calibration._ZN1G = (ushort)xyzN[2];

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


    private bool write_results_to_status_file()
    {
        try
        {
            //save test status to file
            log_file_status = new StreamWriter(log_filename_status);

            for (int i = 0; i < TestResults.Length; i++)
                log_file_status.WriteLine(TestResults[i]);

            log_file_status.Flush();
            log_file_status.Close();
            
            return true;
        }
        catch
        {
            return false;
        }

    }

    #endregion



    #region Close Form


    private void button_finish_Click(object sender, EventArgs e)
    {
        this.Close();
    }


    private void Form_FormClosing(object sender, FormClosingEventArgs e)
    {
        close_form();
    }

    

    private void close_form()
    {

        try
        {
            //close wockets plotter & controller

            //make sure that the bluetooth object is closed
            CurrentWockets._Controller.Dispose();

            //close the logger
            if (log_file != null)
            {
                log_file.Flush();
                log_file.Close();
                log_file = null;
            }

            //close the bat logger
            if (log_file_battery != null)
            {
                log_file_battery.Flush();
                log_file_battery.Close();
                log_file_battery = null;
            }

            //close the pc logger
            if (log_file_pc != null)
            {
                log_file_pc.Flush();
                log_file_pc.Close();
                log_file_pc = null;
            }


           if( ! write_results_to_status_file())
               Console.WriteLine("Problem when writing the status file.");
            else
               Console.WriteLine("The status file was sucessfully written.");


            //write the test results & Xml to file
            //if (!write_results_to_file(TestResults))
            //{ Console.WriteLine("problem writing to test results file"); }


            if (!write_results_to_xml(wc))
                Console.WriteLine("Problem when writing to the xml file.");
            else
                Console.WriteLine("The xml file was sucessfully written.");

        }
        catch(Exception e)
        { Console.WriteLine(e); }

    }


    #endregion



    #region Visualization Thread

    private object visualize_objLock = new object();
    private Thread visualizeThread = null;
    private bool is_visualize_running = false;
    private string notification_result = "";
    private int visualization_sleep_time = 3000;

    public void StartVisualizeThread()
    {
        lock (visualize_objLock)
        {
            if (visualizeThread != null)
                return;

            if (!is_visualize_running)
            {
                visualizeThread = new Thread(new ThreadStart(VisualizeLoop));
                visualizeThread.Start();
            }
        }
    }


    public void StopVisualizeThread()
    {
        lock (visualize_objLock)
        {

            if (visualizeThread == null)
                return;

            if(is_visualize_running)
            {
                is_visualize_running = false;
                visualizeThread.Join();
                 visualizeThread = null;
            }
        }
    }


    private void VisualizeLoop()
    {
        //indicate that the thread has started
        is_visualize_running = true;

        TestNotify(notification_result);

        Thread.Sleep(visualization_sleep_time);

        //indicate that the thread has started
        is_visualize_running = false;
    }




    #endregion




    #region Visualization Functions
    

    // This method is a pattern for making thread-safe
    // calls on a Windows Forms control. 
    //
    // If the calling thread is different from the thread that
    // created the control, this method creates a
    // Delegate/Callback and calls itself asynchronously using the
    // Invoke method.
    //
    // If the calling thread is the same as the thread that created
    // the control, the property is set directly. 
    private int time_between_steps = 2000;
 
    private void Update_Form_SR(double my_sr, int my_tct, int my_trials, string msg)
    {
        // InvokeRequired required compares the thread ID of the
        // calling thread to the thread ID of the creating thread.
        // If these threads are different, it returns true.
        if (this.cal_panel_sr.InvokeRequired)
        {
            DelegateUpdateSRPanel d = new DelegateUpdateSRPanel(Update_Form_SR);
            this.Invoke(d, new object[] {my_sr, my_tct, my_trials, msg });
        }
        else
        {
            if (my_sr == -1.0)
                this.cal_panel_sr.Text = "--";
            else
                this.cal_panel_sr.Text = String.Format( "{0:0.00}", my_sr);

            if( my_tct == -1)
                this.cal_panel_tct.Text = "--";
            else
                this.cal_panel_tct.Text = my_tct.ToString();

            if(my_trials == -1)
                this.cal_panel_trials.Text = "--";
            else
                this.cal_panel_trials.Text = my_trials.ToString();
            

            this.cal_panel_label_status.Text = msg;

        }

        Application.DoEvents();

    }

    private void TestNotify(string result)
    {

        if (this.pictureBox_calibration.InvokeRequired)
        {
            DelegateUpdatePictureBox pb = new DelegateUpdatePictureBox(TestNotify);
            this.Invoke(pb, new object[] { result });
        }
        else
        {
            if (result.CompareTo("success") == 0)
            {
                //----  Indicate the distance test has finished  ------
                //play a sound that the test was finished
                pictureBox_calibration.BackColor = Color.YellowGreen;
            }
            else if (result.CompareTo("failure") == 0)
            {
                //----  Indicate the distance test has finished  ------
                //play a sound that the test was finished
                pictureBox_calibration.BackColor = Color.Tomato;
            }
            else if (result.CompareTo("start") == 0)
            {
                //----  Indicate the distance test has finished  ------
                //play a sound that the test was finished
                pictureBox_calibration.BackColor = Color.Orange;
            }
            else
            {
                pictureBox_calibration.BackColor = Color.DimGray;
            }


            Application.DoEvents();
            playSimpleSound(result);

        }

    }


    #endregion 



    #region SoundPlayer

    private SoundPlayer simpleSound = null;
    private void playSimpleSound(string result)
        {
            try
            {
                bool play_sound = true;

                if (result.CompareTo("success") == 0)
                    simpleSound = new SoundPlayer(@"c:\Windows\Media\Windows XP Print complete.wav");
                else if (result.CompareTo("failure") == 0)
                    simpleSound = new SoundPlayer(@"c:\Windows\Media\Windows XP Critical Stop.wav");
                else if (result.CompareTo("start") == 0)
                    simpleSound = new SoundPlayer(@"c:\Windows\Media\notify.wav");
                else
                    play_sound = false;
                

                if( play_sound )
                     simpleSound.PlaySync();
            }
            catch
            { 
                MessageBox.Show("test sound file not found.");
            }
        }

    #endregion 

   
  
   




}//end Main FormTestWocket class





}//end namespace