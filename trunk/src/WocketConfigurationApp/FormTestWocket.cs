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

        //---- Bluetooth & Wockets ----
        BluetoothDeviceInfo wocket;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        WocketsController wc;

        //---- Commands ---------------
        private string current_command = "";

        //----- calibration panel variables  ------------
        private ushort[] xyzP = new ushort[3] { 0, 0, 0 };
        private ushort[] xyzN = new ushort[3] { 0, 0, 0 };
        private double[] xyzSTD = new double[3] { 0.0, 0.0, 0.0 };

        public static string NEEDED_FILES_PATH = "..\\..\\bin\\NeededFiles\\";
        public static string CALIBRATIONS_DIRECTORY = NEEDED_FILES_PATH + "images\\calibrations\\";
        Image[] calibrationImages;
        int calibration_step = -1;


        //------ Battery Calibration Variables  -------
        public static string BATTERY_DIRECTORY = NEEDED_FILES_PATH + "images\\battery\\";
        private Image[] bat_calibrationImages;
        private int bat_calibration_step = -1;
        bool is_test_finished = true;

        private DateTime StartTime;
        private DateTime CurTime;
        private DateTime TotalTime;
        private TimeSpan OffTime;
        private DateTime StopOffTime;


        //100%, 80%, 60%, 40%, 20%, 10%
        private double[] target_bat_cal_values = new double[6] { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 };
        private double[] bat_cal_values = new double[6] { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 };

        private int CAL_UPDATE_SECS = 10000;
        
        private int StartBTLevel = 0;
        private int CurBTLevel = 0;

        private TextWriter log_file = null;
        private string log_filename = "";
        private string OUTPUT_DIRECTORY = "";

        string[] TestResults = new String[22];


        //------ Sampling Rate Test ------------
        //private int sr_test_step = -1;
        private TimeSpan ElapsedTime = TimeSpan.Zero;
        private TimeSpan MaxTestTime; 

        private int SR = 0;
       

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

            //disable plotter timer
            timerPlotter.Enabled = false;

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
            clean_calibration_values("calibration", true);
            clean_calibration_values("battery_calibration", true);

           
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
            TestResults[19] = ",noise,sdx,0.0";
            TestResults[20] = ",noise,sdy,0.0";
            TestResults[21] = ",noise,sdz,0.0";

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
            cbuffer = new double[MaxSamples ,4];
            //SR = new int[Max_SR_Samples];

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


            //temporal for testing
            #region Update the progress indicators
            
            if ((current_command.Trim().CompareTo("") != 0) &&
                 (!is_test_finished))
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

        }

        private void test_timer_Tick(object sender, EventArgs e)
        {
            
            //this line is commented temporaly for testing
            //if (label_connect_status.Text.Contains("Connected:"))
            //{
                if ((current_command.CompareTo("batery_calibration") == 0) &&
                         (!is_test_finished))
                {
                        #region Send battery level command

                    CurTime = DateTime.Now;
                    TimeSpan TimeDiff = CurTime.Subtract(TotalTime);

                    if (TimeDiff.TotalMilliseconds >= CAL_UPDATE_SECS)
                    {
                        //update the time variables
                        TotalTime = CurTime;

                        // send the command
                        GET_BT cmd = new GET_BT();
                        ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
             
                    }

                    #endregion
                }
               else if ( ( (current_command.CompareTo("calibration") == 0)   ||
                           (current_command.CompareTo("distance_test") == 0) )  
                          && (is_test_finished) && (!is_reading) )
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
                        //process_sr_response(response);
                        break;
                    case ResponseTypes.BP_RSP:
                        info_cmd_value_BatteryTest.Text = ((BP_RSP)response)._Percent.ToString() + "%";
                        break;
                    case ResponseTypes.PC_RSP:
                        info_cmd_value_distance_test.Text = ((PC_RSP)response)._Count.ToString();
                        break;
                   case ResponseTypes.BTCAL_RSP:
                       info_cmd_value_BatteryTest.Text = ((BTCAL_RSP)response)._CAL100.ToString() + " " + ((BTCAL_RSP)response)._CAL80.ToString() + " " + ((BTCAL_RSP)response)._CAL60.ToString() + " " + ((BTCAL_RSP)response)._CAL40.ToString() + " " + ((BTCAL_RSP)response)._CAL20.ToString() + " " + ((BTCAL_RSP)response)._CAL10.ToString();
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

        private void process_sr_response()
        {
            if ((current_command.CompareTo("sampling_rate") == 0)
                && (!is_test_finished))
            {
                
                if (log_file != null)
                {
                    //Log the data 
                    DateTime timenow = DateTime.Now;
                    log_file.WriteLine( timenow.ToShortDateString() + " " + 
                                        String.Format("{0:HH:mm:ss.fff}", timenow) + "," + 
                                       "sampling_rate" );
                }

                //Stop the test reached the maximum elapsed time 
                TimeSpan diff = ElapsedTime.Subtract(MaxTestTime);
                    

                if ( diff.TotalSeconds >= 0.0 )
                {   
                   
                    //Finish the test
                    is_test_finished = true;
                    calibration_step = 1;
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

        
        private void plotToolStripMenuItem_Click(object sender, EventArgs e)
        {
            plotData();
        }


        #region commented
        Form3 plotterForm = null;
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
        #endregion commented


        #region commented new graphing
        /*
        private WocketsScalablePlotter rawdataPlotter;
        private Bitmap backBuffer = null;
        //private bool isResized = false;
        
        private void plotData()
        {
          if (CurrentWockets._Controller != null)
            {
                if (!plotToolStripMenuItem.Checked)
                {
                    if ((rawdataPlotter == null) || (!panelPlotter.Visible))
                    {
                        rawdataPlotter = new WocketsScalablePlotter(this.panelPlotter, CurrentWockets._Controller);
                        timerPlotter.Enabled = true;
                       
                        if (!panelPlotter.Visible)
                            panelPlotter.Visible = true;
                    }

                }
                else
                {

                    if (rawdataPlotter != null)
                    {
                        panelPlotter.Visible = false;
                        timerPlotter.Enabled = false;
                    }
                }
            }
        }



       private void timerPlotter_Tick(object sender, EventArgs e)
       {
           GraphAccelerometerValues();
       }


       
       /// <param name="pevent"></param>
       //protected override void OnPaintBackground(PaintEventArgs pevent)
       //{
       //}

       void panelPlotter_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
       {
           if ((this.panelPlotter.Visible) && (backBuffer != null))
               e.Graphics.DrawImage(backBuffer, 0, 0);
       }


       #region commented
       //void Form3_Resize(object sender, System.EventArgs e)
       //{
       //    this.timer1.Enabled = false;
       //    this.panel1.Width = this.Width;
       //    this.panel1.Height = this.Height;
       //    aPlotter = new WocketsScalablePlotter(this.panel1, CurrentWockets._Controller);
       //    isResized = true;
       //    this.timer1.Enabled = true;
       //}
       #endregion commented


       private void GraphAccelerometerValues()
       {
           if ( backBuffer == null ) //|| (isResized))
           {
               backBuffer = new Bitmap((int)this.panelPlotter.Width, (int)this.panelPlotter.Height);
               //isResized = false;
           }
           using (Graphics g = Graphics.FromImage(backBuffer))
           {
               rawdataPlotter.Draw(g);
               g.Dispose();
           }

       }

        */
        #endregion 




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


        #region EVENTS

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

                   cal_panel_values_BTpercent.Visible = false;

                   //calibration panel
                   cal_panel_cal_values.Visible = false;
                   cal_panel_cal_values_positive.Visible = true;
                   cal_panel_cal_values_negative.Visible = true;
                   cal_panel_cal_values_std.Visible = true;


                   //progress bar
                   cal_panel_progressBar.Visible = false;


                   //buttons
                   button_load.Enabled = false;
                   button_finish.Enabled = false;

                 
                   //calibration panel
                   panel_calibration.Visible = true;
                   
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
                   cal_panel_bat_label_elapTime.Text = "";
                   cal_panel_bat_label_startTime.Text = "";
                   
                   //start calibration steps
                   calibration_step = 0;
                   cal_panel_button_ok.Enabled = true;
                   info_cmd_value_WKTCalibration.Text = "Calibrating ...";
                   clean_calibration_values("calibration",true);
                  

                   #endregion Calibration
               }
               else if (current_command.CompareTo("distance_test") == 0)
               {
                   #region Distance Test

                   //Plot Data
                   plotToolStripMenuItem.Checked = false;
                   plotData();


                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_distance_test.Text;
                   

                   cal_panel_label_status.Text = "Position the wocket as shown in the picture.\r\n" +
                                                 "Use a surface with NO MOVEMENT or VIBRATION. \r\n" +
                                                 "Click NEXT when ready.\r\n";


                   cal_panel_button_ok.Text = "Next";

                   //Sampling Rate Log File
                   log_filename = OUTPUT_DIRECTORY +
                                  wocket.DeviceAddress.ToString().Substring(7) + "_" +
                                  "DT_Log.txt";
                   log_file = new StreamWriter(log_filename);


                   //progress bar
                   cal_panel_progressBar.Visible = true;
                   cal_panel_progressBar.Value = 0;


                   //picture box
                   pictureBox_calibration.Size = new Size(358, 240);
                   pictureBox_calibration.Visible = true;
                   pictureBox_calibration.Image = calibrationImages[4];


                   //clean panel parameters
                   panel_status_texbox.Text = "";
                   panel_status.Visible = false;
                   cal_panel_bat_label_elapTime.Text = "";
                   cal_panel_bat_label_startTime.Text = "";

                   //Hide battery Panel
                   cal_panel_values_BTpercent.Visible = false;

                   //set calibration panel
                   cal_panel_cal_values.Visible = false;
                   cal_panel_cal_values_positive.Visible = true;
                   cal_panel_cal_values_negative.Visible = false;
                   cal_panel_cal_values_std.Visible = true;


                   //Hide select folder fields
                   //cal_panel_cmd_label.Text = "Path";
                   //cal_panel_entry_path.Text = "";
                   cal_panel_entry_path.Enabled = false;
                   cal_panel_entry_path.Visible = false;
                   cal_panel_cmd_label.Visible = false;
                   cal_panel_button_browse.Enabled = false;
                   cal_panel_button_browse.Visible = false;


                   //--- calibration panel  ---
                   panel_calibration.Visible = true;


                   //initialize test steps
                   calibration_step = 0;
                   cal_panel_button_ok.Enabled = true;
                   info_cmd_value_distance_test.Text = "Testing...";
                   clean_calibration_values("calibration", true);

                   #endregion Distance Test

               }
               else if (current_command.CompareTo("sampling_rate") == 0)
               {
                   #region Sampling Rate Test

                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_SamplingRate.Text;
                   
                   cal_panel_label_status.Text = "Place the wocket in a surface with NO MOVEMENT \r\n" +
                                                 "or VIBRATION as shown in the picture.\r\n" +
                                                 "When ready, click START.";

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
                   cal_panel_bat_label_elapTime.Text = "";
                   cal_panel_bat_label_startTime.Text = "";

                   //battery value Panel
                   cal_panel_values_BTpercent.Visible = false;

                   
                   //set calibration panel
                   cal_panel_cal_values.Visible = false;
                   cal_panel_cal_values_positive.Visible = true;
                   cal_panel_cal_values_negative.Visible = false;
                   cal_panel_cal_values_std.Visible = true;

                   //Hide select folder fields
                   //cal_panel_cmd_label.Text = "Path";
                   //cal_panel_entry_path.Text = "";
                   cal_panel_entry_path.Enabled = false;
                   cal_panel_entry_path.Visible = false;
                   cal_panel_cmd_label.Visible = false;
                   cal_panel_button_browse.Enabled = true;
                   cal_panel_button_browse.Visible = false;


                   //calibration panel
                   panel_calibration.Visible = true;

                   #region commented
                   //start battery calibration steps
                  // sr_test_step = 0;
                   //cal_panel_button_ok.Enabled = true;
                   //info_cmd_value_SamplingRate.Text = "Testing Sampling Rate...";
                   #endregion

                   //initialize test steps
                   calibration_step = 0;
                   cal_panel_button_ok.Enabled = true;
                   info_cmd_value_SamplingRate.Text = "Testing Sampling Rate...";
                   clean_calibration_values("calibration", true);


                   #endregion Sampling Rate Test

               

               }
               else if (current_command.CompareTo("battery_calibration") == 0)
               {
                   #region Battery Calibration
                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_BatteryTest.Text;
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
                   cal_panel_bat_label_elapTime.Text = "";
                   cal_panel_bat_label_startTime.Text = "";


                   //Hide Value Panels
                   cal_panel_values_BTpercent.Visible = false;
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
                   info_cmd_value_BatteryTest.Text = "Calibrating Battery";
                   clean_calibration_values("battery_calibration", true);
                   pictureBox_calibration.Image = null;

                   #endregion BAT Calibration
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

       
        private void cal_panel_button_cancel_Click(object sender, EventArgs e)
        {
            //restore status panel
            restore_status_panel();

            if (current_command.CompareTo("calibration") == 0)
            { info_cmd_value_WKTCalibration.Text = "No Calibrated"; }
            else if (current_command.CompareTo("battery_calibration") == 0)
            { info_cmd_value_BatteryTest.Text = "No Calibrated"; }
            else if (current_command.CompareTo("sampling_rate") == 0)
            { info_cmd_value_SamplingRate.Text = "No Tested"; }
            else if (current_command.CompareTo("distance_test") == 0)
            { info_cmd_value_distance_test.Text = "No Tested"; }
   
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
        
     
        //---  Calibration Test  ---------
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
            OffTime = TimeSpan.Zero;
            StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);


            //Flag that determines if the axis standard deviations need to be computed
            if (compute_std)
                CALIBRATE_STD = true;
              

            //Enable timer
            test_timer.Enabled = true;
            test_timer.Start();


            //Start the reading thread for calibration
            StartReading();

        }


        private string stop_axis_calibration(string axis_name, bool skip_position_step, 
                                             string next_axis_name, int image_number)
        {
            string calibration_result = "";

                   
            //--- stop test  ----
            is_test_finished = true;


            //-- disable timer  ---
            test_timer.Stop();
            test_timer.Enabled = false;


            //--- Get the computed variables  ----
            if (compute_calibration_stats(axis_name, out calibration_result) == 0)
            {
                //if calibration stats successful, pass to the next step
                calibration_step++;

                //---  show the std dev results  -----
                if (CALIBRATE_STD)
                {
                    cal_panel_xstd.Text = String.Format("{0:0.00}", xyzSTD[0]);
                    cal_panel_ystd.Text = String.Format("{0:0.00}", xyzSTD[1]);
                    cal_panel_zstd.Text = String.Format("{0:0.00}", xyzSTD[2]);
                }

               
                //setup the ui for the next test
                if (!skip_position_step)
                {
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "Continue";
                    //cal_panel_label_status.Text = "The " + axis_name + " axis calibration has finished.\r\n";
                    cal_panel_label_status.Text = "The calibration process has finished.\r\n" +
                                                  "Click CONTINUE to save the data.";


                    //update progres bar 
                    cal_panel_progressBar.Value = 100;
                }
                else
                {
                    //skip position step
                    if (image_number > 0)
                        position_axis_calibration(next_axis_name, image_number);
                    
                }
            }
            else
            {
                cal_panel_button_ok.Enabled = true;
                cal_panel_button_ok.Text = "Try Again";
                   
                cal_panel_label_status.Text = "The test has finished.\r\n" +
                                              "The calibration DATA WAS NOT collected successfully.\r\n" +
                                              "Press Try Again, to run the test again.";
                
                //perform the calibration again
                calibration_step --;
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



        //---- Distance Test  -------
        private void start_distance_test(string distance)
        {
            cal_panel_button_ok.Enabled = false;
            cal_panel_button_ok.Text = "START";
            cal_panel_label_status.Text = "Testing the wocket at " + distance + " of distance.\r\n" +
                                          "DO NOT MOVE the wocket while testing";

            //values for panel calibration
            cal_panel_cal_values.Visible = true;
            
            
            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;

            
            // start calibration & initialize time counters
            is_test_finished = false;
            OffTime = TimeSpan.Zero;
            StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);


            //Flag that determines if the axis standard deviations need to be computed
            CALIBRATE_STD = true;


            //Enable timer
            test_timer.Enabled = true;
            test_timer.Start();


            //Start the reading thread for calibration
            StartReading();

           
        }

        private string stop_distance_test(string distance, string next_distance, bool is_saving)
        {
            string calibration_result = "";

            //--- stop test  ----
            is_test_finished = true;


            //-- disable timer  ---
            test_timer.Stop();
            test_timer.Enabled = false;


            //--- Get the computed variables  ----
            if (compute_calibration_stats("all", out calibration_result) == 0)
            {
                //if data was successfully collected, pass to the next step
                calibration_step++;


                //update text fields
                cal_panel_x1g.Text = String.Format("{0:0.00}", xyzP[0]);
                cal_panel_y1g.Text = String.Format("{0:0.00}", xyzP[1]);
                cal_panel_z1g.Text = String.Format("{0:0.00}", xyzP[2]);


                //---  show the std dev results  -----
                if (CALIBRATE_STD)
                {
                    cal_panel_xstd.Text = String.Format("{0:0.00}", xyzSTD[0]);
                    cal_panel_ystd.Text = String.Format("{0:0.00}", xyzSTD[1]);
                    cal_panel_zstd.Text = String.Format("{0:0.00}", xyzSTD[2]);

                    calibration_result = calibration_result +
                                        String.Format("{0:0.00}", xyzSTD[0]) + "," +
                                        String.Format("{0:0.00}", xyzSTD[1]) + "," +
                                        String.Format("{0:0.00}", xyzSTD[2]) ;
                }



                //save to log file
                if (log_file != null)
                {
                    log_file.WriteLine( distance + "," +
                                        StartTime.ToString() + "," +
                                        ElapsedTime.ToString() + "," +
                                        calibration_result);
                }


                //setup the ui for the next test
                cal_panel_button_ok.Enabled = true;
                //cal_panel_label_status.Text = "The test has finished.\r\n";
                cal_panel_label_status.Text = "";


                if (!is_saving)
                {
                    cal_panel_button_ok.Text = "Continue";
                    cal_panel_label_status.Text = cal_panel_label_status.Text +
                                                  "Now, place the wocket " + next_distance + " away from the computer.\r\n" +
                                                  "Click CONTINUE to save the data.";
                }
                else
                {
                    cal_panel_button_ok.Text = "Save";
                    cal_panel_label_status.Text = cal_panel_label_status.Text +
                                                 "Click SAVE to save the data.";
                }

                //update progres bar 
                cal_panel_progressBar.Value = 100;
                
               //play a sound that the test was finished
               // playSimpleSound();
            }
            else
            {
                cal_panel_button_ok.Enabled = true;
                cal_panel_button_ok.Text = "Try Again";

                cal_panel_label_status.Text = "The test has finished.\r\n" +
                                              "The DATA WAS NOT collected successfully.\r\n" +
                                              "Click TRY AGAIN, to repeat the test.";

                //perform the calibration again
                calibration_step--;
            }


            //reset the compute std. dev. flag
            CALIBRATE_STD = false;


            return calibration_result;

        }

        
        //---- Sampling Rate Test -----
        private void start_SamplingRate_test(int test_time)
        {
            
            cal_panel_button_ok.Enabled = false;
            cal_panel_button_ok.Text = "PAUSE";
            cal_panel_label_status.Text = "Running Sampling Rate Test...\r\n" +
                                          "Keep the wocket in the SAME POSITION.\r\n" +
                                          "Click CANCEL if you want to exit.";

            //values for panel calibration
            cal_panel_cal_values.Visible = true;
            cal_panel_cal_values_positive.Visible = true;
            cal_panel_cal_values_negative.Visible = false;
            cal_panel_cal_values_std.Visible = true;

            //progress bar
            cal_panel_progressBar.Value = 0;
            cal_panel_progressBar.Visible = true;


            //Start calibration & initialize time counters
            is_test_finished = false;
            OffTime = TimeSpan.Zero;
            StartTime = DateTime.Now;
            cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);

            //Test Time (in minutes)
            MaxTestTime= new TimeSpan(0, test_time, 0);  

            //Flag that determines if the axis standard deviations need to be computed
            CALIBRATE_STD = true;


            //Enable timer
            test_timer.Enabled = true;
            test_timer.Start();


            //Start the reading thread for calibration
            StartReading();


        }

        private string stop_SamplingRate_test()
        {
            string test_result = "";

            //--- stop test  ----
            is_test_finished = true;

            //-- disable timer  ---
            test_timer.Stop();
            test_timer.Enabled = false;


            //--- Get the computed variables  ----
            if (compute_calibration_stats("all", out test_result) == 0)
            {
                //if data was successfully collected, pass to the next step
                calibration_step++;


                //update text fields
                cal_panel_x1g.Text = String.Format("{0:0.00}", xyzP[0]);
                cal_panel_y1g.Text = String.Format("{0:0.00}", xyzP[1]);
                cal_panel_z1g.Text = String.Format("{0:0.00}", xyzP[2]);


                //---  show the std dev results  -----
                if (CALIBRATE_STD)
                {
                    cal_panel_xstd.Text = String.Format("{0:0.00}", xyzSTD[0]);
                    cal_panel_ystd.Text = String.Format("{0:0.00}", xyzSTD[1]);
                    cal_panel_zstd.Text = String.Format("{0:0.00}", xyzSTD[2]);

                    test_result = test_result +
                                        String.Format("{0:0.00}", xyzSTD[0]) + "," +
                                        String.Format("{0:0.00}", xyzSTD[1]) + "," +
                                        String.Format("{0:0.00}", xyzSTD[2]);
                }



                //save to log file
                if (log_file != null)
                {
                    log_file.WriteLine( "sampling_rate" + "," +
                                        StartTime.ToString() + "," +
                                        ElapsedTime.ToString() + "," +
                                        test_result);
                }


                //setup the ui for the next test
                cal_panel_button_ok.Enabled = true;
                cal_panel_label_status.Text = "";

                cal_panel_button_ok.Text = "Save";
                cal_panel_label_status.Text = "Click SAVE to keep the data.";
                

                //update progres bar 
                cal_panel_progressBar.Value = 100;
  
            }
            else
            {
                cal_panel_button_ok.Enabled = true;
                cal_panel_button_ok.Text = "Try Again";

                cal_panel_label_status.Text = "The test has finished.\r\n" +
                                              "The DATA WAS NOT collected successfully.\r\n" +
                                              "Click TRY AGAIN, to repeat the test.";

                //perform the calibration again
                calibration_step--;
            }


            //reset the compute std. dev. flag
            CALIBRATE_STD = false;


            return test_result;

        }




        //--- Process the test ----
        private void process_calibration()
        {
            if (current_command.CompareTo("calibration") == 0)
            {

                #region Wocket Calibration

                if (calibration_step == 0)
                {
                  
                    start_axis_calibration("X +G", false);
            
                }
                else if(calibration_step == 1)
                {
                  cal_panel_x1g.Text = stop_axis_calibration("X +G",true,"Y +G", 2);
                }
                else if (calibration_step == 2)
                {
                    position_axis_calibration("Y +G", 2);
                }
                else if (calibration_step == 3)
                {
                    start_axis_calibration("Y +G",false);   
                }
                else if (calibration_step == 4)
                {
                    //update the calibrated variable
                    cal_panel_y1g.Text = stop_axis_calibration("Y +G", true, "X -G", 1);
                }
                else if (calibration_step == 5)
                {
                    position_axis_calibration("X -G", 1);
  
                }
                else if (calibration_step == 6)
                {
                    start_axis_calibration("X -G", false);

                }
                else if (calibration_step == 7)
                {
                    //update the calibrated variable
                    cal_panel_xn1g.Text = stop_axis_calibration("X -G", true, "Y -G", 3);

                }
                else if (calibration_step == 8)
                {
                   position_axis_calibration("Y -G", 3);

                }
                else if (calibration_step == 9)
                {
                    start_axis_calibration("Y -G", false);

                }
                else if (calibration_step == 10)
                {
                    
                   //update the calibrated variable
                    cal_panel_yn1g.Text = stop_axis_calibration("Y -G", true, "Z -G", 5);
                }
                else if (calibration_step == 11)
                {
                    position_axis_calibration("Z -G", 5);
                 }
                else if (calibration_step == 12)
                {
                   start_axis_calibration("Z -G", false);
                }
                else if (calibration_step == 13)
                {
                    //update the calibrated variable
                    cal_panel_zn1g.Text = stop_axis_calibration("Z -G", true, "Z +G", 4);

                }
                else if (calibration_step == 14)
                {
                   position_axis_calibration("Z +G", 4);
                }
                else if (calibration_step == 15)
                {
                   start_axis_calibration("Z +G", true);
                }
                else if (calibration_step == 16)
                {
                    
                   //update the calibrated variable
                    cal_panel_z1g.Text = stop_axis_calibration("Z +G",false,"",0);

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
                    info_cmd_value_WKTCalibration.Text = "Last Calibration: " + String.Format("{0:MM/dd/yy  HH:mm:ss}", timenow);

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Calibration Test Finished.";

                    #endregion

                    //clean up the steps
                    calibration_step = -1;

                }

                #endregion Calibration

            }
            else if (current_command.CompareTo("distance_test") == 0)
            {

                #region Distance Test

                if (calibration_step == 0)
                {
                    cal_panel_button_ok.Enabled = true;
                    cal_panel_button_ok.Text = "START";
                    cal_panel_label_status.Text = "Place the wocket " + "1 METER" + " away from computer.\r\n" +
                                                  "When ready, click START.";

                    calibration_step = 1;
                }
                else if (calibration_step == 1)
                {
                    start_distance_test("1 METER");
                }
                else if (calibration_step == 2)
                {
                    stop_distance_test("1 METER", "5 METERS", false);
                }
                else if (calibration_step == 3)
                {
                    start_distance_test("5 METERS");
                }
                else if (calibration_step == 4)
                {
                    stop_distance_test("5 METERS", "10 METERS", false);
                }
                else if (calibration_step == 5)
                {
                    start_distance_test("10 METERS");
                }
                else if (calibration_step == 6)
                {
                    stop_distance_test("10 METERS", "15 METERS", false);
                }
                else if (calibration_step == 5)
                {
                    start_distance_test("15 METERS");
                }
                else if (calibration_step == 6)
                {
                    stop_distance_test("15 METERS", "", true);
                }
                else if (calibration_step == 7)
                {
                    finish_save_to_string(current_command);
                }

                #endregion Distance Test
            }
            else if (current_command.CompareTo("sampling_rate") == 0)
            {
                #region Sampling Rate Test

                //Initialize Sampling Rate test
                if (calibration_step == 0)
                {
                  
                    start_SamplingRate_test(1);

                } //Pause/Stop test
                else if (calibration_step == 1)
                {
                    stop_SamplingRate_test();

                }
                //Restart Calibration test
                else if (calibration_step == 2)
                {
                  finish_save_to_string("sampling_rate");
                }
               
               
                #endregion Sampling Rate Test

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
                    cal_panel_values_BTpercent.Visible = true;
                    cal_panel_values_BTpercent.Visible = true;
                    Application.DoEvents();

                    // start battery calibration & initialize time counters
                    is_test_finished = false;
                    OffTime = TimeSpan.Zero;
                    StartTime = DateTime.Now;
                    cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);

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
                    StopOffTime = DateTime.Now;

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
                    cal_panel_values_BTpercent.Visible = true;
                    Application.DoEvents();

                    // start battery calibration
                    is_test_finished = false;
                    //OffTime = TimeSpan.Zero;
                    //StartTime = DateTime.Now;
                    //cal_panel_bat_label_startTime.Text = String.Format("{0:HH:mm:ss}", StartTime);
                    OffTime = OffTime.Add(DateTime.Now.Subtract(StopOffTime));


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
                    info_cmd_value_BatteryTest.Text = "Calibrated on " + String.Format("{0:HH:mm:ss}");

                    panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                               timenow.ToString() + ": Battery Calibration Test Finished.";



                    #endregion

                }

                #endregion Battery Calibration

            }
            
        }


        private void finish_save_to_string(string cmd_name)
        {
            //Get the current time
            DateTime timenow = DateTime.Now;

            //save results
            string stime = String.Format("{0:MM-dd-yy}", timenow) + " " +
                           String.Format("{0:HH:mm:ss}", timenow);

            //Save values to the test results string
            if ( cmd_name.CompareTo("distance_test") == 0)
            {
                //TestResults[10] = stime + ",sampling_rate,sr," + "";
                TestResults[19] = stime + ",noise,xstd," + xyzSTD[0].ToString();
                TestResults[20] = stime + ",noise,ystd," + xyzSTD[1].ToString();
                TestResults[21] = stime + ",noise,zstd," + xyzSTD[2].ToString();

                //update the test status
                info_cmd_value_distance_test.Text = "Last Test: " + String.Format("{0:MM/dd/yy  HH:mm:ss}", timenow);

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           String.Format("{0:MM/dd/yy  HH:mm:ss}", timenow) + ": Distance Test Finished.";
            }
            else if (cmd_name.CompareTo("sampling_rate") == 0)
            {
                //TestResults[10] = stime + ",sampling_rate,sr," + "";
                TestResults[19] = stime + ",noise,xstd," + xyzSTD[0].ToString();
                TestResults[20] = stime + ",noise,ystd," + xyzSTD[1].ToString();
                TestResults[21] = stime + ",noise,zstd," + xyzSTD[2].ToString();

                //update the test status
                info_cmd_value_SamplingRate.Text = "Last Test: " + String.Format("{0:MM/dd/yy  HH:mm:ss}", timenow);

                panel_status_texbox.Text = panel_status_texbox.Text + "\r\n" +
                                           String.Format("{0:MM/dd/yy  HH:mm:ss}", timenow) + ": Sampling Rate Test Finished.";
            }

            //---- Finish the calibration process ------
            // Determine the axis standard deviations
            cal_panel_label_status.Text = "";

            //Close calibration panel 
            restore_status_panel();

            //clean up the steps
            calibration_step = -1;

        }

        private void restore_status_panel()
        {
            
            //Disable timer
            test_timer.Enabled = false;
            test_timer.Stop();
                
            StartBTLevel = 0;
            OffTime = TimeSpan.Zero;

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
           panel_status.Visible = true;

            //clean calibration panel
            cal_panel_title.Text = "";
            cal_panel_cmd_label.Text = "";
            cal_panel_entry_path.Text = "";

            clean_calibration_values("",false);

            cal_panel_values_BTpercent.Visible = false;
            cal_panel_cal_values.Visible = false;

            panel_calibration.Visible = false;
            
            //buttons
            button_load.Enabled = true;
            button_finish.Enabled = true;
            button_start_test.Enabled = true;
            button_to_xml.Enabled = true;

            //reset variables
            is_test_finished = true;

            //Close Data Plotter
            plotToolStripMenuItem.Checked = true;
            plotData();

            Application.DoEvents();

            //Stop Reading The Thread
            StopReading();


        }

        private void clean_calibration_values(string cmd_name, bool clean_array)
        {

            if (cmd_name.CompareTo("calibration") == 0)
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
                    xyzP[0] = 0;
                    xyzP[1] = 0;
                    xyzP[2] = 0;

                    xyzN[0] = 0;
                    xyzN[1] = 0;
                    xyzN[2] = 0;

                    xyzSTD[0] = 0.0;
                    xyzSTD[1] = 0.0;
                    xyzSTD[2] = 0.0;
                }

            }
            else if (cmd_name.CompareTo("battery_calibration") == 0)
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

        private SoundPlayer simpleSound = null; 
        private void playSimpleSound()
        {
            try
            {
                if (simpleSound == null)
                { simpleSound= new SoundPlayer(@"c:\Windows\Media\chimes.wav");}

                simpleSound.PlaySync();
            }
            catch
            { 
                MessageBox.Show("test sound file not found.");
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
                acc_sensor._Calibration._X1G = xyzP[0];
                acc_sensor._Calibration._Y1G = xyzP[1];
                acc_sensor._Calibration._Z1G = xyzP[2];

                acc_sensor._Calibration._XN1G = xyzN[0];
                acc_sensor._Calibration._YN1G = xyzN[1];
                acc_sensor._Calibration._ZN1G = xyzN[2];

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
                acc_sensor._Calibration._X1G = xyzP[0];
                acc_sensor._Calibration._Y1G = xyzP[1];
                acc_sensor._Calibration._Z1G = xyzP[2];

                acc_sensor._Calibration._XN1G = xyzN[0];
                acc_sensor._Calibration._YN1G = xyzN[1];
                acc_sensor._Calibration._ZN1G = xyzN[2];

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
                #region comment
                //if (plotterForm != null)
                //{
                //    plotterForm.Close();
                //    plotterForm = null;
                //}
                #endregion comment

                //write the test results & Xml to file
            if (!write_results_to_file(TestResults))
            { Console.WriteLine("problem writing to test results file"); }

        }

        #endregion





    #region Compute Calibration 

    private double[] RMEANS = new double[3]{0.0, 0.0, 0.0};
    private double[] RSTD   = new double[3] { 0.0, 0.0, 0.0 };

    private long samplingRate = 0;
    private DateTime calTime;
    
    private int MaxSamples = 20000;
    
    private int DecodedPackets = 0;
    private bool is_reading = false;

    private double[,] cbuffer;
    private bool CALIBRATE_STD = false;

    //Thread
    private object _objLock = new object();
    private Thread readingThread = null;

       

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


        MaxSamples = 1000;

        // Initialize the means
        double[] accMeans = new double[3] { 0.0, 0.0, 0.0 };
        RMEANS[0] = 0.0;
        RMEANS[1] = 0.0;
        RMEANS[2] = 0.0;
        RSTD[0] = 0.0;
        RSTD[1] = 0.0;
        RSTD[2] = 0.0;



        // Initialize the buffer 
        // where the decoded data will be temp. storaged
        clean_data_buffer();

        // Initialize counter
        DecodedPackets = 0;
         
        // Initialize buffer pointers
        // The wockets controller doesn't keep track of the tail
        // it needs to be initialized to the head
        int myHead = wc._Decoders[0]._Head; 
        int myTail = myHead;
        Wockets.Data.Accelerometers.AccelerationData data;


        try
        {
            if (calibration_step == 0)
            {
                calTime = DateTime.Now;
                samplingRate = wc._Decoders[0].TotalSamples;
            }

            is_reading = true;

           

            #region Get Data Samples

            //-- Loop until the desired number of samples ---
            while ( (DecodedPackets < MaxSamples) && 
                    (is_reading))
            {

                
                //wait and update the head, when the tail has reached the head 
                if (myTail == myHead)
                {  System.Threading.Thread.Sleep(1000);
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

                    //add data to buffer
                    cbuffer[DecodedPackets, 0] = data._X;
                    cbuffer[DecodedPackets, 1] = data._Y;
                    cbuffer[DecodedPackets, 2] = data._Z;
                    cbuffer[DecodedPackets, 3] = data.UnixTimeStamp;
                    //update the number of decoded packets
                    DecodedPackets++;
                }


                //update the tail
                if (myTail >= wc._Decoders[0]._Data.Length - 1)
                    myTail = 0;
                else
                    myTail++;

            }//ends while



            //compute the final mean result
            if (DecodedPackets > 1)
            {
                for (int i = 0; i < 3; i++)
                {
                    //compute the mean
                    RMEANS[i] = accMeans[i] / DecodedPackets;
                }


                //if (CALIBRATE_STD)
                if(true)
                {   //compute the standard deviation
                    for (int k = 0; k < 3; k++)
                    {
                        for (int j = 0; j < DecodedPackets; j++)                        
                            RSTD[k] = RSTD[k] + Math.Pow(cbuffer[j, k] - RMEANS[k], 2.0);                                                
                        RSTD[k] = Math.Sqrt(RSTD[k] / DecodedPackets);                        
                    }
                }
            }

            
            //Finish Test & Update Delegate
            calibration_step = calibration_step + 1;

            if (calibration_step == 16)      
                samplingRate = (long) Math.Round(((wc._Decoders[0].TotalSamples-samplingRate) / ((TimeSpan)DateTime.Now.Subtract(calTime)).TotalSeconds));            


        }//ends try
        catch
        {
            DecodedPackets = -1;
        }
             

        #endregion 


       
       
       //Indicate that the reading loop ended
        is_reading = false;
        is_test_finished = true;
        

    }//function ends

    


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
                    xyzP[0] = Convert.ToUInt16(RMEANS[0]);
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


                    st_result = String.Format("{0:0} ", xyzP[0]) + "," +
                                String.Format("{0:0} ", xyzP[1]) + "," +
                                String.Format("{0:0} ", xyzP[2]) + ",";
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

    private void clean_data_buffer()
    {
        if (cbuffer.Length > 0 )
        {
            for (int i=0; i < MaxSamples; i++)
            {    for (int j = 0; j < 4; j++)
                    cbuffer[i, j] = 0.0;
            }
        }
    }


    #endregion 

  

   

    
   
      


    }//end class
}//end namespace