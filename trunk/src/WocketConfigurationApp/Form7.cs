using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

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
    public partial class Form7 : Form
    {
        #region Declare Variables

        BluetoothDeviceInfo wocket;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        WocketsController wc;

        //private string latestReading;
        private string current_command = "";
      
        private double[] xyzP    = new double[3] {0.0,0.0,0.0};
        private double[] xyzN    = new double[3] {0.0,0.0,0.0 };
        private double[] xyzSTD  = new double[3] { 0.0, 0.0, 0.0 };

        private string cur_tr_mode = "";
        private int cur_sampling_rate = 90;
        private string cur_sensitivity = "";
        private int cur_power_down = 90;

        private bool is_sensordata_valid = false;
        
        #endregion


        #region Initialize

        public Form7(BluetoothDeviceInfo wocket)
        {
            InitializeComponent();

            //Copy parameters to loacal variables
            this.wocket = wocket;
            this.Text = "Wocket (" + wocket.DeviceAddress.ToString() + ")";

            //Load the parameters saved on the bluetoothinfo device
            this.info_cmd_value_name.Text = wocket.DeviceName;
            this.info_cmd_value_mac.Text = wocket.DeviceAddress.ToString();
            this.panel_status_texbox.Text = "";

            this.panel_status.Visible = true;
            this.panel_calibration.Visible = false;
            
            clean_calibration_values();


            //load sensitivity values
            info_cmd_value_sensitivity.Items.Clear();
            info_cmd_value_sensitivity.Items.Add("");
            info_cmd_value_sensitivity.Items.Add("1.5 G");
            info_cmd_value_sensitivity.Items.Add("2 G");
            info_cmd_value_sensitivity.Items.Add("4 G");
            info_cmd_value_sensitivity.Items.Add("6 G");
            info_cmd_value_sensitivity.Items.Add("8 G");
            info_cmd_value_sensitivity.SelectedIndex = 0;

            //info_cmd_value_sensitivity.FlatStyle = FlatStyle.Flat;
            //info_cmd_value_sensitivity.AllowSelection = false;
           
            //load transmission mode values
            info_cmd_value_tr_rate.Items.Clear();
            info_cmd_value_tr_rate.Items.Add("");
            info_cmd_value_tr_rate.Items.Add("Continuous");
            info_cmd_value_tr_rate.Items.Add("Burst Mode 30 secs");
            info_cmd_value_tr_rate.Items.Add("Burst Mode 60 secs");
            info_cmd_value_tr_rate.Items.Add("Burst Mode 90 secs");
            info_cmd_value_tr_rate.Items.Add("Burst Mode 120 secs");
            info_cmd_value_tr_rate.SelectedIndex = 0;
            

            //info_cmd_value_tr_rate.FlatStyle = FlatStyle.Flat;
            //info_cmd_value_tr_rate.Enabled= false;


        }


        private void Form2_Load(object sender, EventArgs e)
        {
            //wocket controller object
            InitializeWocket();

            //commands
            LoadWocketsParameters();

            //Hide the setting panels
            //panel_calibration.Visible = false;
            //panel_status.Visible = true;
            //set_panel_cmd_entry_combo.Visible = false;
            //set_panel_cmd_entry_textbox.Visible = false;

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
                    case ResponseTypes.BL_RSP:
                        info_cmd_value_battery_level.Text = ((BL_RSP)response)._BatteryLevel.ToString();
                        break;
                    case ResponseTypes.BP_RSP:
                        info_cmd_value_btpercent.Text = ((BP_RSP)response)._Percent.ToString() + "%";
                        break;
                    case ResponseTypes.SENS_RSP:
                        //info_cmd_value_sensitivity.Text = ((SENS_RSP)response)._Sensitivity.ToString() + " G";
                        load_sensitivity_field(((SENS_RSP)response)._Sensitivity.ToString());
                        break;
                    case ResponseTypes.SR_RSP:
                        cur_sampling_rate = ((SR_RSP)response)._SamplingRate;
                        info_cmd_value_sampling_rate.Text = cur_sampling_rate.ToString();
                        break;
                    case ResponseTypes.TM_RSP:
                        //info_cmd_value_tr_rate.Text = ((TM_RSP)response)._TransmissionMode.ToString();
                        load_trmode_field(((TM_RSP)response)._TransmissionMode.ToString());
                        break;
                    case ResponseTypes.CAL_RSP:
                        info_cmd_value_calibration.Text = ((CAL_RSP)response)._X1G.ToString() + " " + ((CAL_RSP)response)._XN1G.ToString() + " " + ((CAL_RSP)response)._Y1G.ToString() + " " + ((CAL_RSP)response)._YN1G.ToString() + " " + ((CAL_RSP)response)._Z1G.ToString() + " " + ((CAL_RSP)response)._ZN1G.ToString();
                        break;
                    case ResponseTypes.PC_RSP:
                        info_cmd_value_pkt_count.Text = ((PC_RSP)response)._Count.ToString() + " - " + ((WocketsDecoder)wc._Decoders[0])._UncompressedPDUCount + " - " + ((WocketsDecoder)wc._Decoders[0])._CompressedPDUCount;
                        break;
                    case ResponseTypes.PDT_RSP:
                        //info_cmd_value_pwr_timeout.Text = ((PDT_RSP)response)._Timeout.ToString();
                        cur_power_down = ((PDT_RSP)response)._Timeout;
                        info_cmd_value_pwr_timeout.Text = cur_power_down.ToString();
                        break;
                    case ResponseTypes.BTCAL_RSP:
                       info_cmd_value_btcalibration.Text = ((BTCAL_RSP)response)._CAL100.ToString() + " " + ((BTCAL_RSP)response)._CAL80.ToString() + " " + ((BTCAL_RSP)response)._CAL60.ToString() + " " + ((BTCAL_RSP)response)._CAL40.ToString() + " " + ((BTCAL_RSP)response)._CAL20.ToString() + " " + ((BTCAL_RSP)response)._CAL10.ToString();
                        break;
                    case ResponseTypes.HV_RSP:
                        info_cmd_value_hwversion.Text = ((HV_RSP)response)._Version.ToString();
                        break;
                    case ResponseTypes.FV_RSP:
                       info_cmd_value_swversion.Text = ((FV_RSP)response)._Version.ToString();
                        break;
                    
                    default:
                        break;
                }

                this.Refresh();
            }
        }


        #endregion


        #region Reconnect & Timer


        private void timer1_Tick(object sender, EventArgs e)
        {

            if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Disconnected)
                this.label_connection_status.Text = "Disconnected";
            else if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Reconnecting)
                this.label_connection_status.Text = "Reconnecting";
            else
            {

                if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Data)
                    this.label_connection_status.Text = "Connected: Data Mode";
                else
                    this.label_connection_status.Text = "Connected: Command Mode";
            }

        }

        #endregion


        #region old code
        
        private void comboBox1_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Command)
            {
                /*Command c = new GET_BR();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(c._Bytes);*/
            }
        }

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
                        plotterForm.Close();
                        plotterForm = null;
                    }
                }

            }

        #endregion


        //------  Close & CleanUp panel   --------
        #region Close & Clean up panels
        
        //private void set_panel_button_close_Click(object sender, EventArgs e)
        //{
        //    set_panel_cleanup();
        //}

        //private void set_panel_cleanup()
        //{
        //    if (current_command.CompareTo("name") == 0)
        //    {
        //        set_panel_cmd_entry_textbox.Text = "";
        //        set_panel_cmd_entry_textbox.Visible = false;
        //        //info_button_name.Enabled = true;
        //    }
        //    else if (current_command.CompareTo("sensitivity") == 0)
        //    {
        //        set_panel_cmd_entry_combo.Visible = false;
        //        //info_button_sensitivity.Enabled = true;
        //    }
        //    else if (current_command.CompareTo("tr_mode") == 0)
        //    {
        //        set_panel_cmd_entry_combo.Visible = false;
        //        //info_button_tr_rate.Enabled = true;
        //    }
        //    else if (current_command.CompareTo("sampling_rate") == 0)
        //    {
        //        set_panel_cmd_entry_textbox.Text = "";
        //        set_panel_cmd_entry_textbox.Visible = false;
        //        //info_button_sampling_rate.Enabled = true;
        //    }
        //    else if (current_command.CompareTo("pwr_timeout") == 0)
        //    {
        //        set_panel_cmd_entry_textbox.Text = "";
        //        set_panel_cmd_entry_textbox.Visible = false;
        //        //info_button_pwr_timeout.Enabled = true;
        //    }
        //    else if (current_command.CompareTo("calibration") == 0)
        //    {
        //        cal_panel_entry_path.Text = "";
        //        cal_panel_entry_path.Visible= false;
        //        //info_button_calibration.Enabled = true;

        //        panel_calibration.Visible = false;
        //        cal_panel_label_status.Text = "";
        //        cal_panel_cmd_label.Text = "";
        //        cal_panel_title.Text = "";

        //    }
        //    else if (current_command.CompareTo("alive") == 0)
        //    {
        //        set_panel_cmd_entry_textbox.Text = "";
        //        set_panel_cmd_entry_textbox.Visible = false;
        //        //info_button_alive.Enabled = true;
        //    }


        //    current_command = "";

        //    panel_status.Visible = false;
        //    panel_status_texbox.Text = "";
        //    set_panel_cmd_label.Text = "";
        //    set_panel_title.Text = "";

        //}

        //private void set_panel_setup(string title, string label, string value, bool text_on) 
        //{

        //    set_panel_title.Text = title;
        //    set_panel_cmd_label.Text = label;
           


        //    if (text_on)
        //    {
        //        set_panel_cmd_entry_textbox.Text = value;

        //        set_panel_cmd_entry_textbox.Visible = true;
        //        set_panel_cmd_entry_textbox.Enabled = true;

        //        set_panel_cmd_entry_combo.Visible = false;
        //        set_panel_cmd_entry_combo.Enabled = false;
        //    }
        //    else
        //    {

        //        set_panel_cmd_entry_textbox.Visible = false;
        //        set_panel_cmd_entry_textbox.Enabled = false;

        //        set_panel_cmd_entry_combo.Visible = true;
        //        set_panel_cmd_entry_combo.Enabled = true;
        //    }

        //    set_panel_button_set.Enabled = true;
        //    set_panel_button_close.Enabled = true;

        //    panel_status.Visible = true;
        
        //}


        //Click the "set" button in the configuration panel
        //private void set_panel_button_set_Click(object sender, EventArgs e)
        //{
        //    try
        //    {
        //        set_panel_button_set.Enabled = false;
        //        Application.DoEvents();

        //        if (current_command.CompareTo("name") == 0)
        //        {
                   
        //            //set the name that the user entered in the set textbox 
        //            info_cmd_value_name.Text = set_panel_cmd_entry_textbox.Text;
                   
        //        }
        //        else if (current_command.CompareTo("sensitivity") == 0)
        //        {
        //            //info_button_sensitivity.Enabled = false;
        //            //Application.DoEvents();

        //           int index = set_panel_cmd_entry_combo.SelectedIndex;
        //           string strval = set_panel_cmd_entry_combo.Items[index].ToString();


        //            //set the sensitivity level selected in the combo box
        //           if (index > 0)
        //           {
        //               //string value = strval.Split(' ')[0];
        //               info_cmd_value_sensitivity.Text = strval;
        //               //info_button_sensitivity.Enabled = true;
        //               set_panel_label_status.Text = "";
        //           }
        //           else
        //           {
        //               set_panel_label_status.Text = "Select a valid entry from the pull down menu.";
        //           }
                    
        //        }
        //        else if (current_command.CompareTo("tr_mode") == 0)
        //        {
        //            int index = set_panel_cmd_entry_combo.SelectedIndex;
        //            string strval = set_panel_cmd_entry_combo.Items[index].ToString();
                    
        //            //set the transmission mode selected in the combo box
        //            if (index > 0)
        //            {
        //                if (strval.CompareTo("Continuous") == 0)
        //                {
        //                    //set the wockets to transmit in countinous mode
        //                    cur_tr_mode = "continous";
                            
        //                }
        //                else
        //                {
        //                    string burst_value = strval.Split(' ')[2];
        //                    //set the wockets to transmit in countinous mode
        //                    cur_tr_mode = burst_value;
        //                }


        //                info_cmd_value_tr_rate.Text = strval;
        //                set_panel_label_status.Text = "";
        //            }
        //            else
        //            {
        //                set_panel_label_status.Text = "Select a valid entry from the pull down menu.";
        //            }

        //        }
        //        else if (current_command.CompareTo("sampling_rate") == 0)
        //        {
        //            bool outOfrange = false;
        //            int val = 0;

        //            //get the sampling rate
        //            if (set_panel_cmd_entry_textbox.Text.Trim().CompareTo("") != 0)
        //                val = Int32.Parse(set_panel_cmd_entry_textbox.Text);


        //            //set the sampling rate according with the transmission mode
        //            if (cur_tr_mode.CompareTo("continuous") == 0)
        //            {
        //                if (val >= 1 && val <= 126)
        //                {
        //                    //set the wockets sampling rate in countinous mode
        //                    info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
        //                }
        //                else
        //                    outOfrange = true;
        //            }
        //            else if (cur_tr_mode.CompareTo("30") == 0)
        //            {
        //                if (val >= 1 && val <= 80)
        //                {
        //                    //set the wockets sampling rate in burst 30 secs mode
        //                    info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
        //                }
        //                else
        //                    outOfrange = true;
        //            }
        //            else if (cur_tr_mode.CompareTo("60") == 0)
        //            {
        //                if (val >= 1 && val <= 40)
        //                {
        //                    //set the wockets sampling rate in burst 60 secs mode
        //                    info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
        //                }
        //                else
        //                    outOfrange = true;
        //            }
        //            else if (cur_tr_mode.CompareTo("90") == 0)
        //            {
        //                if (val >= 1 && val <= 30)
        //                {
        //                    //set the wockets sampling rate in burst 90 secs mode
        //                    info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
        //                }
        //                else
        //                    outOfrange = true;
        //            }
        //            else if (cur_tr_mode.CompareTo("120") == 0)
        //            {
        //                if (val >= 1 && val <= 20)
        //                {
        //                    //set the wockets sampling rate in burst 90 secs mode
        //                    info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
        //                }
        //                else
        //                    outOfrange = true;
        //            }



        //            if (outOfrange == true)
        //            {
        //                set_panel_label_status.Text = set_panel_label_status.Text + "\n\r Sampling rate out of range.";
        //                info_cmd_value_sampling_rate.Text = "out of range";
        //            }
        //        }
        //        else if (current_command.CompareTo("pwr_timeout") == 0)
        //        {
        //            bool outOfrange = false;
        //            int val = 0;

        //            //get the sampling rate
        //            if (set_panel_cmd_entry_textbox.Text.Trim().CompareTo("") != 0)
        //                val = Int32.Parse(set_panel_cmd_entry_textbox.Text);


        //            //set the power down timeout  according the permitted range in minutes
        //            if (val >= 1 && val <= 127)
        //            {
        //                //set the wockets sampling rate in countinous mode
        //                info_cmd_value_pwr_timeout.Text = val.ToString() + " Hz";
        //            }
        //            else
        //            {
        //                set_panel_label_status.Text = "The time you entered is out of range. /n/r The power down timeout range is between 1 min and 127 minutes.";
        //                info_cmd_value_pwr_timeout.Text = "out of range";
        //            }
        //        }
        //        else if (current_command.CompareTo("alive") == 0)
        //        {
        //            bool outOfrange = false;
        //            int val = 0;

        //            //get the alive timeout
        //            if (set_panel_cmd_entry_textbox.Text.Trim().CompareTo("") != 0)
        //                val = Int32.Parse(set_panel_cmd_entry_textbox.Text);


        //            //set the alive timeout  according the permitted range in seconds
        //            if (val >= 10)
        //            {
        //                //set the alive timeout in seconds
        //                // //info_cmd_value_alive.Text = val.ToString() + " Secs";
        //            }
        //            else
        //            {
        //                set_panel_label_status.Text = "The time you entered is too short. /n/r The alive timeout minimum value is 10 seconds.";
        //                // //info_cmd_value_alive.Text = "?";
        //            }
        //        }
                    

        //        set_panel_button_set.Enabled = true;
                
        //    }
        //    catch
        //    {
        //        set_panel_button_set.Enabled = true;

        //        if (set_panel_cmd_entry_combo.Visible == true)
        //            set_panel_cmd_entry_combo.SelectedIndex = 0;
        //        else if (set_panel_cmd_entry_textbox.Visible == true)
        //            set_panel_cmd_entry_textbox.Text = "";


        //    }
        //}
        
        
        #endregion 


        //-------  Commands -----------------------
       // load sensitivity to field
        // 0="", 1= 1.5, 2=2.0, 3=4.0, 4=6.0, 5=8.0
        private void load_sensitivity_field(string val)
        { 
           if( val.Contains("1.5") )
           { info_cmd_value_sensitivity.SelectedIndex = 1; }
           else if (val.Contains("2"))
           { info_cmd_value_sensitivity.SelectedIndex = 2; }
           else if (val.Contains("4"))
           { info_cmd_value_sensitivity.SelectedIndex = 3; }
           else if (val.Contains("6"))
           { info_cmd_value_sensitivity.SelectedIndex = 4; }
           else if (val.Contains("8"))
           { info_cmd_value_sensitivity.SelectedIndex = 5; }
           else
           { info_cmd_value_sensitivity.SelectedIndex = 0; }

           cur_sensitivity = (string)info_cmd_value_sensitivity.Items[info_cmd_value_sensitivity.SelectedIndex];

        }

        // load transmission mode to field
        // 0="", 1= Cont, 2=30, 3=60, 4=90, 5=120
        private void load_trmode_field(string val)
        {
            if (val.Contains("Continuous"))
            { info_cmd_value_tr_rate.SelectedIndex = 1; }
            else if (val.Contains("30"))
            { info_cmd_value_tr_rate.SelectedIndex = 2; }
            else if (val.Contains("60"))
            { info_cmd_value_tr_rate.SelectedIndex = 3; }
            else if (val.Contains("90"))
            { info_cmd_value_tr_rate.SelectedIndex = 4; }
            else if (val.Contains("120"))
            { info_cmd_value_tr_rate.SelectedIndex = 5; }
            else
            { info_cmd_value_tr_rate.SelectedIndex = 0; }

            cur_tr_mode = (string)info_cmd_value_tr_rate.Items[info_cmd_value_tr_rate.SelectedIndex];
        }


        //--------------------------------------
        //private void set_sensitivity_field(string val)
        //{
        //    int id = 0;

        //    try
        //    {
        //        if (val.Contains("1.5"))
        //        {

        //            id = 1;
        //        }
        //        else if (val.Contains("2"))
        //        { id = 2; }
        //        else if (val.Contains("4"))
        //        { id = 3; }
        //        else if (val.Contains("6"))
        //        { id = 4; }
        //        else if (val.Contains("8"))
        //        { id = 5; }
        //        else
        //        { id = 0; }
        //    }
        //    catch
        //    {
        //        id = 0;
        //    }


        //    info_cmd_value_sensitivity.SelectedIndex = id;

        //}


        //name

        #region commands
        //private void set_name()
        //{
        //    //set_panel_cleanup();
        //    //current_command = "name";

        //    //set_panel_setup(info_cmd_label_name.Text, info_cmd_label_name.Text, info_cmd_value_name.Text, true);

        //    ////info_button_name.Enabled = false;

        //}

        ////hardware version
        //private void load_hw_version()
        //{
        //    //set_panel_cleanup();

        //    //current_command = "hw_version";

        //    //try
        //    //{
        //    //    //info_button_hwversion.Enabled = false;
        //    //    //Application.DoEvents();

        //    //    //querry the hw version 
        //    //    //set the hw version
        //    //    //info_cmd_value_hwversion.Text = "Rev. 3";
        //    //    //info_button_hwversion.Enabled = true;

        //    //}
        //    //catch
        //    //{
        //    //    // error
        //    //    //info_cmd_value_hwversion.Text = "Error, version not loaded.";
        //    //    //info_button_hwversion.Enabled = true;
        //    //}

        //    //current_command = "";
        //}

        ////software version
        //private void load_swversion()
        //{
        //    ////set_panel_cleanup();

        //    //current_command = "sw_version";

        //    //try
        //    //{
        //    //    //info_button_swversion.Enabled = false;
        //    //    //Application.DoEvents();

        //    //    ////querry the sw version 
        //    //    ////set the sw version
        //    //    //info_cmd_value_swversion.Text = "Rev. 3";

        //    //    //info_button_swversion.Enabled = true;

        //    //}
        //    //catch
        //    //{
        //    //    //// error
        //    //    //info_cmd_value_swversion.Text = "Error, version not loaded.";
        //    //    //info_button_swversion.Enabled = true;
        //    //}

        //    //current_command = "";
        //}


        ////packet count
        //private void load_pc()
        //{
        //    //set_panel_cleanup();
        //    //current_command = "packet_count";

        //    //try
        //    //{
        //    //    info_button_pkt_count.Enabled = false;
        //    //    Application.DoEvents();

        //    //    //get the packets count
        //    //    info_cmd_value_pkt_count.Text = get_packet_count();

        //    //    info_button_pkt_count.Enabled = true;

        //    //}
        //    //catch
        //    //{
        //    //    // error
        //    //    info_cmd_value_pkt_count.Text = "Error.Packet count not loaded.";
        //    //    info_button_pkt_count.Enabled = true;
        //    //}

        //    //current_command = "";
        //}

        //private string get_packet_count()
        //{
        //    string val = "?";

        ////    //try
        ////    //{
        ////    //    //GET_PC pc = new GET_PC();
        ////    //    //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(pc._Bytes);
        ////    //    //val = pc._Bytes[0].ToString();
        ////    //}
        ////    //catch
        ////    //{
        ////    //    val = "?";
        ////    //}

        //    return val;
        //}


        
        
        ////batery level
        //private void load_battery_level()
        //{

        //    //set_panel_cleanup();
        //    //current_command = "battery";

        //    //try
        //    //{
        //    //    info_button_battery_level.Enabled= false;
        //    //    Application.DoEvents();

        //    //    //querry the battery level 
        //    //    //set the battery level
        //    //    info_cmd_value_battery_level.Text = get_battery_level();

        //    //    info_button_battery_level.Enabled = true;

        //    //}
        //    //catch
        //    //{
        //    //    // error
        //    //    info_cmd_value_battery_level.Text = "Error.Battery level not loaded.";
        //    //    info_button_battery_level.Enabled = true;
        //    //}

        //    //current_command = "";
        //}

        //private string get_battery_level()
        //{
        //    string val = "?";

        ////    try
        ////    {
        ////        //GET_BT bt_level = new GET_BT();
        ////        //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(bt_level._Bytes);
        ////        //val = bt_level._Bytes.ToString();
        ////    }
        ////    catch 
        ////    {
        ////        val = "?";
        ////    }

        //    return val;
        //}


        ////calibration
        //private void load_calibration()
        //{
        //    //set_panel_cleanup();

        //    //current_command = "calibration";
        //    //info_cmd_value_calibration.Text = get_sensor_calibration();

        //    ////prepare the calibration panel
        //    //cal_panel_title.Text = info_cmd_label_calibration.Text;
        //    //cal_panel_cmd_label.Text = info_cmd_label_calibration.Text;
        //    //cal_panel_entry_path.Text = "";
        //    //cal_panel_label_status.Text = "";

        //    //cal_panel_entry_path.Visible = true;
        //    //panel_calibration.Visible = true;
            
        //    //info_button_calibration.Enabled = false;

        //}

        //private string get_sensor_calibration()
        //{
        //    string val = "?";

        //    //try
        //    //{
        //    //    //GET_CAL cal = new GET_CAL();
        //    //    //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cal._Bytes);
        //    //   // val = cal._Bytes.ToString();
        //    //}
        //    //catch
        //    //{
        //    //    val = "?";
        //    //}

        //    return val;
        //}
        

        ////calibration  panel buttons
        //private void cal_panel_button_browse_Click(object sender, EventArgs e)
        //{
        //    try
        //    {
        //       //check the path selected in the textbox
        //        this.folderBrowserDialog1.ShowNewFolderButton = false;

        //       if (cal_panel_entry_path.Text.Trim().CompareTo("") != 0)
        //        {
        //            if (Directory.Exists(cal_panel_entry_path.Text))
        //            { this.folderBrowserDialog1.SelectedPath = cal_panel_entry_path.Text.ToString(); }
        //            else
        //            { this.folderBrowserDialog1.RootFolder = System.Environment.SpecialFolder.Desktop; }
        //        }
        //        else
        //        {
        //            this.folderBrowserDialog1.RootFolder = System.Environment.SpecialFolder.Desktop;
        //        }


        //       //check the path selected in the dialog
        //       DialogResult result = this.folderBrowserDialog1.ShowDialog();


        //       if (result == DialogResult.OK)
        //       {
        //           string fullPath = this.folderBrowserDialog1.SelectedPath;
        //           cal_panel_entry_path.Text = fullPath;

        //           if (cal_panel_entry_path.Text.Trim().CompareTo("") == 0)
        //           {
        //               cal_panel_label_status.Text = "Please provide a valid path";
        //           }
        //           else
        //           {
        //               if(current_command.CompareTo("calibration") == 0)
        //               {
        //                   //it is a valid sensordata file with calibration values
        //                   //open the sensordata file and get the calibration values   
        //                   cal_panel_label_status.Text = "The sensordata file is valid. You can set the CAL values.";
        //                   is_sensordata_valid = true;
        //               }
        //               else if (current_command.CompareTo("battery_calibration") == 0)
        //               {
        //                   // it is a valid sensordata file with calibration values
        //                   //open the battery calibration file and get the cal values   
        //                   cal_panel_label_status.Text = "The battery calibration file is valid. You can set the CAL values.";
        //                   is_sensordata_valid = true;
        //               }
        //           }
        //       }


        //    } // end try

        //    catch (Exception err)
        //    {
        //        Console.WriteLine(err.Message);
        //    }
        //}



        ////private void cal_panel_button_set_Click(object sender, EventArgs e)
        ////{

        ////    //cal_panel_button_set.Enabled = false;

        ////    //if (cal_panel_entry_path.Text.Trim().CompareTo("") == 0)
        ////    //{
        ////    //    cal_panel_label_status.Text = "Please provide a valid path";
        ////    //}
        ////    //else
        ////    //{
        ////    //    // if is a valid path
        ////    //    // check if it is a valid file
        ////    //    // open the file and get the calibration values

        ////    //    //set status
        ////    //    cal_panel_label_status.Text = "The CAL values were set.";
        ////    //}

        ////    //cal_panel_button_set.Enabled = true;

        ////}
       
        ////private void cal_panel_button_close_Click(object sender, EventArgs e)
        ////{
        ////    //set_panel_cleanup();
        ////}

      
        ////sensitivity
        
        ////private void button_set_sensitivity_Click(object sender, EventArgs e)
        ////{
        ////    //set_panel_cleanup();

        ////    //current_command = "sensitivity";

        ////    //info_cmd_value_sensitivity.Text = get_sensor_sensitivity();

        ////    ////add sensitivity options to combo box
        ////    //set_panel_cmd_entry_combo.Items.Clear();
        ////    //set_panel_cmd_entry_combo.Items.Add("");
        ////    //set_panel_cmd_entry_combo.Items.Add("1.5 g");
        ////    //set_panel_cmd_entry_combo.Items.Add("2.0 g");
        ////    //set_panel_cmd_entry_combo.Items.Add("4.0 g");
        ////    //set_panel_cmd_entry_combo.Items.Add("6.0 g");
        ////    //set_panel_cmd_entry_combo.SelectedIndex = 0;

        ////    ////prepare the set panel
        ////    //set_panel_setup(info_cmd_label_sensitivity.Text, info_cmd_label_sensitivity.Text, "", false);

           
        ////    //info_button_sensitivity.Enabled = false;

        ////}

        ////private string get_sensor_sensitivity()
        ////{
        ////    //string val = "?";

        ////    //try
        ////    //{
        ////    //    GET_SEN sen = new GET_SEN();
        ////    //    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(sen._Bytes);
        ////    //    val = sen._Bytes[0].ToString();
        ////    //}
        ////    //catch
        ////    //{
        ////    //    val = "?";
        ////    //}

        ////    //return val;
        ////}


        ////transmission mode
        
        
        //private void info_button_tr_rate_Click(object sender, EventArgs e)
        //{
        //    //set_panel_cleanup();

        //    //current_command = "tr_mode";

        //    ////add sensitivity options to combo box
        //    //set_panel_cmd_entry_combo.Items.Clear();
        //    //set_panel_cmd_entry_combo.Items.Add("");
        //    //set_panel_cmd_entry_combo.Items.Add("Continuous");
        //    //set_panel_cmd_entry_combo.Items.Add("Burst Mode 30 secs");
        //    //set_panel_cmd_entry_combo.Items.Add("Burst Mode 60 secs");
        //    //set_panel_cmd_entry_combo.Items.Add("Burst Mode 90 secs");
        //    //set_panel_cmd_entry_combo.Items.Add("Burst Mode 120 secs");
        //    //set_panel_cmd_entry_combo.SelectedIndex = 0;

        //    ////prepare the set panel
        //    //set_panel_setup(info_cmd_label_tr_rate.Text, info_cmd_label_tr_rate.Text, "", false);

        //    ////read the current saved value

        //    ////disable button
        //    //info_button_tr_rate.Enabled = false;

        //}


        ////sampling rate

        //private void info_button_sampling_rate_Click(object sender, EventArgs e)
        //{
        //    //set_panel_cleanup();

        //    //current_command = "sampling_rate";

        //    ////prepare the set panel
        //    //set_panel_setup(info_cmd_label_sampling_rate.Text, info_cmd_label_sampling_rate.Text, "", true);

        //    ////disable the sampling rate button
        //    //info_button_sampling_rate.Enabled = false;



        //    ////send cmd
        //    ////GET_SR cmd = new GET_SR();
        //    ////((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);


        //    ////select the allowed sampling rate
        //    //if (cur_tr_mode.CompareTo("continous") == 0)
        //    //{
        //    //    set_panel_label_status.Text = "The Wockets is set to continous mode. \n\r This mode supports sampling rates between 1Hz and 126Hz. \n\r Enter the sampling rate in the command textbox.";
                
        //    //    //SET_SR set_sr_cmd = new SET_SR(90);
        //    //    //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(set_sr_cmd._Bytes);
        //    //}
        //    //else if (cur_tr_mode.CompareTo("30") == 0)
        //    //{
        //    //    set_panel_label_status.Text = "The Wockets is set to burst 30 secs mode. \n\r This mode supports sampling rates between 1Hz and 80Hz. \n\r Enter the sampling rate in the command textbox.";
        //    //}
        //    //else if (cur_tr_mode.CompareTo("60") == 0)
        //    //{
        //    //    set_panel_label_status.Text = "The Wockets is set to burst 60 secs mode. \n\r This mode supports sampling rates between 1Hz and 40Hz. \n\r Enter the sampling rate in the command textbox.";
        //    //}
        //    //else if (cur_tr_mode.CompareTo("90") == 0)
        //    //{
        //    //    set_panel_label_status.Text = "The Wockets is set to burst 90 secs mode. \n\r This mode supports sampling rates between 1Hz and 30Hz. \n\r Enter the sampling rate in the command textbox.";
        //    //}
        //    //else if (cur_tr_mode.CompareTo("120") == 0)
        //    //{
        //    //    set_panel_label_status.Text = "The Wockets is set to burst 120 secs mode. \n\r This mode supports sampling rates between 1Hz and 20Hz. \n\r Enter the sampling rate in the command textbox.";
        //    //}
        //    //else if (cur_tr_mode.CompareTo("") == 0)
        //    //{
        //    //    set_panel_label_status.Text = "Before setting up the sampling rate, it is necessary specify the transmission mode.";
        //    //}       

        //}

        ////power timeout
        //private void info_button_pwr_timeout_Click(object sender, EventArgs e)
        //{
        //    //set_panel_cleanup();

        //    //current_command = "pwr_timeout";

        //    ////prepare the set panel
        //    //set_panel_setup(info_cmd_label_pwr_timeout.Text, info_cmd_label_pwr_timeout.Text, "", true);

        //    ////read the current saved value

        //    ////disable button
        //    //info_button_pwr_timeout.Enabled= false;

        //}


        #endregion 

        
       

        #region Change Fields Functions
        //---change field status functions -------------
        
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
                    if (current_command.CompareTo(cur_cmd) != 0)
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


        private void cleanup_fields(string cmd)
        {
            if (current_command.CompareTo("all") != 0)
            {
                switch (cmd)
                {
                    case "hw_version":
                        current_command = "";
                        info_cmd_value_hwversion.BackColor = Color.DimGray;
                        info_cmd_value_hwversion.ForeColor = Color.White;
                        info_cmd_label_hwversion.ForeColor = Color.Orange;
                        break;
                    case "sw_version":
                        current_command = "";
                        info_cmd_value_swversion.BackColor = Color.DimGray;
                        info_cmd_value_swversion.ForeColor = Color.White;
                        info_cmd_label_swversion.ForeColor = Color.Orange;
                        break;
                    case "packet_count":
                        current_command = "";
                        info_cmd_value_pkt_count.BackColor = Color.DimGray;
                        info_cmd_value_pkt_count.ForeColor = Color.White;
                        info_cmd_label_pkt_count.ForeColor = Color.Orange;
                        break;
                    case "battery_level":
                        current_command = "";
                        info_cmd_value_battery_level.BackColor = Color.DimGray;
                        info_cmd_value_battery_level.ForeColor = Color.White;
                        info_cmd_label_battery.ForeColor = Color.Orange;
                        break;
                    case "battery_percent":
                        current_command = "";
                        info_cmd_value_btpercent.BackColor = Color.DimGray;
                        info_cmd_value_btpercent.ForeColor = Color.White;
                        info_cmd_label_btpercent.ForeColor = Color.Orange;
                        break;
                    case "battery_calibration":
                        current_command = "";
                        info_cmd_value_btcalibration.BackColor = Color.DimGray;
                        info_cmd_value_btcalibration.ForeColor = Color.White;
                        info_cmd_label_btcalibration.ForeColor = Color.Orange;
                        break;
                    case "calibration":
                        current_command = "";
                        info_cmd_value_calibration.BackColor = Color.DimGray;
                        info_cmd_value_calibration.ForeColor = Color.White;
                        info_cmd_label_calibration.ForeColor = Color.Orange;
                        break;
                    case "sensor_sensitivity":
                        current_command = "";
                        info_cmd_value_sensitivity.BackColor = Color.DimGray;
                        info_cmd_value_sensitivity.ForeColor = Color.White;
                        info_cmd_label_sensitivity.ForeColor = Color.Orange;
                        break;
                    case "transmission_mode":
                        current_command = "";
                        info_cmd_value_tr_rate.BackColor = Color.DimGray;
                        info_cmd_value_tr_rate.ForeColor = Color.White;
                        info_cmd_label_tr_rate.ForeColor = Color.Orange;
                        break;
                    case "sampling_rate":
                        current_command = "";
                        info_cmd_value_sampling_rate.BackColor = Color.DimGray;
                        info_cmd_value_sampling_rate.ForeColor = Color.White;
                        info_cmd_label_sampling_rate.ForeColor = Color.Orange;
                        break;
                    case "power_down":
                        current_command = "";
                        info_cmd_value_pwr_timeout.BackColor = Color.DimGray;
                        info_cmd_value_pwr_timeout.ForeColor = Color.White;
                        info_cmd_label_pwr_timeout.ForeColor = Color.Orange;
                        break;
                }
            }
        }

        private void disable_all_fields()
        { 
             current_command = "";

             //"hw_version":
                  info_cmd_value_hwversion.BackColor = Color.DimGray;
                  info_cmd_value_hwversion.ForeColor = Color.White;
                  info_cmd_label_hwversion.ForeColor = Color.Orange;
                  
              //"sw_version":
                  info_cmd_value_swversion.BackColor = Color.DimGray;
                  info_cmd_value_swversion.ForeColor = Color.White;
                  info_cmd_label_swversion.ForeColor = Color.Orange;
                  
              //"packet_count":
                  info_cmd_value_pkt_count.BackColor = Color.DimGray;
                  info_cmd_value_pkt_count.ForeColor = Color.White;
                  info_cmd_label_pkt_count.ForeColor = Color.Orange;
                 
              //"battery_level":
                  info_cmd_value_battery_level.BackColor = Color.DimGray;
                  info_cmd_value_battery_level.ForeColor = Color.White;
                  info_cmd_label_battery.ForeColor = Color.Orange;
                  
              //"battery_percent":
                  info_cmd_value_btpercent.BackColor= Color.DimGray;
                  info_cmd_value_btpercent.ForeColor = Color.White;
                  info_cmd_label_btpercent.ForeColor = Color.Orange;
                  
             //"battery_calibration":
                  info_cmd_value_btcalibration.BackColor = Color.DimGray;
                  info_cmd_value_btcalibration.ForeColor = Color.White;
                  info_cmd_label_btcalibration.ForeColor = Color.Orange;
             
            //"calibration":
                  info_cmd_value_calibration.BackColor = Color.DimGray;
                  info_cmd_value_calibration.ForeColor = Color.White;
                  info_cmd_label_calibration.ForeColor = Color.Orange;
            
            // "sensor_sensitivity":
                  info_cmd_value_sensitivity.BackColor = Color.DimGray;
                  info_cmd_value_sensitivity.ForeColor = Color.White;
                  info_cmd_label_sensitivity.ForeColor = Color.Orange;
           
            // "transmission_mode":
                  info_cmd_value_tr_rate.BackColor= Color.DimGray;
                  info_cmd_value_tr_rate.ForeColor = Color.White;
                  info_cmd_label_tr_rate.ForeColor = Color.Orange;
           
            // "sampling_rate":
                  info_cmd_value_sampling_rate.BackColor = Color.DimGray;
                  info_cmd_value_sampling_rate.ForeColor = Color.White;
                  info_cmd_label_sampling_rate.ForeColor = Color.Orange;
                  
            // "power_down":
                  info_cmd_value_pwr_timeout.BackColor = Color.DimGray;
                  info_cmd_value_pwr_timeout.ForeColor = Color.White;
                  info_cmd_label_pwr_timeout.ForeColor = Color.Orange;
                  
        }

        private void enable_all_fields()
        {
            current_command = "all";

            //"hw_version":
            info_cmd_value_hwversion.BackColor = Color.WhiteSmoke;
            info_cmd_value_hwversion.ForeColor = Color.Black;
            info_cmd_label_hwversion.ForeColor = Color.WhiteSmoke;

            //"sw_version":
            info_cmd_value_swversion.BackColor = Color.WhiteSmoke;
            info_cmd_value_swversion.ForeColor = Color.Black;
            info_cmd_label_swversion.ForeColor = Color.WhiteSmoke;

            //"packet_count":
            info_cmd_value_pkt_count.BackColor = Color.WhiteSmoke;
            info_cmd_value_pkt_count.ForeColor = Color.Black;
            info_cmd_label_pkt_count.ForeColor = Color.WhiteSmoke;

            //"battery_level":
            info_cmd_value_battery_level.BackColor = Color.WhiteSmoke;
            info_cmd_value_battery_level.ForeColor = Color.Black;
            info_cmd_label_battery.ForeColor = Color.WhiteSmoke;

            //"battery_percent":
            info_cmd_value_btpercent.BackColor = Color.WhiteSmoke;
            info_cmd_value_btpercent.ForeColor = Color.Black;
            info_cmd_label_btpercent.ForeColor = Color.WhiteSmoke;

            //"battery_calibration":
            info_cmd_value_btcalibration.BackColor = Color.WhiteSmoke;
            info_cmd_value_btcalibration.ForeColor = Color.Black;
            info_cmd_label_btcalibration.ForeColor = Color.WhiteSmoke;

            //"calibration":
            info_cmd_value_calibration.BackColor = Color.WhiteSmoke;
            info_cmd_value_calibration.ForeColor = Color.Black;
            info_cmd_label_calibration.ForeColor = Color.WhiteSmoke;

            // "sensor_sensitivity":
            info_cmd_value_sensitivity.BackColor = Color.WhiteSmoke;
            info_cmd_value_sensitivity.ForeColor = Color.Black;
            info_cmd_label_sensitivity.ForeColor = Color.WhiteSmoke;

            // "transmission_mode":
            info_cmd_value_tr_rate.BackColor = Color.WhiteSmoke;
            info_cmd_value_tr_rate.ForeColor = Color.Black;
            info_cmd_label_tr_rate.ForeColor = Color.WhiteSmoke;

            // "sampling_rate":
            info_cmd_value_sampling_rate.BackColor = Color.WhiteSmoke;
            info_cmd_value_sampling_rate.ForeColor = Color.Black;
            info_cmd_label_sampling_rate.ForeColor = Color.WhiteSmoke;

            // "power_down":
            info_cmd_value_pwr_timeout.BackColor = Color.WhiteSmoke;
            info_cmd_value_pwr_timeout.ForeColor = Color.Black;
            info_cmd_label_pwr_timeout.ForeColor = Color.WhiteSmoke;

        }

        
        private void info_panel_clean_text_fields()
        {
            info_cmd_value_battery_level.Text = "";
            info_cmd_value_sampling_rate.Text = "";
            info_cmd_value_tr_rate.Text = "";
            info_cmd_value_btpercent.Text = "";
            info_cmd_value_sensitivity.Text = "";
            info_cmd_value_calibration.Text = "";
            info_cmd_value_pkt_count.Text = "";
            info_cmd_value_pwr_timeout.Text = "";
            info_cmd_value_btcalibration.Text = "";
            info_cmd_value_hwversion.Text = "";
            info_cmd_value_swversion.Text = "";
        }

        //---------------------------------------//
        #endregion



        #region EVENTS

        private void info_cmd_value_swversion_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_swversion,info_cmd_value_swversion, e.KeyCode, "sw_version");

        }

        private void info_cmd_value_hwversion_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_hwversion,info_cmd_value_hwversion, e.KeyCode, "hw_version");
        }


        private void info_cmd_value_pkt_count_KeyDown(object sender, KeyEventArgs e)
        {
            change_status_field(info_cmd_label_pkt_count,info_cmd_value_pkt_count,e.KeyCode, "packet_count");
        }


       private void info_cmd_value_battery_level_KeyDown(object sender, KeyEventArgs e)
       {
            change_status_field(info_cmd_label_battery,info_cmd_value_battery_level, e.KeyCode, "battery_level");
       }

       private void info_cmd_value_btpercent_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_btpercent,info_cmd_value_btpercent, e.KeyCode, "battery_percent");
       }

       private void info_cmd_value_btcalibration_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_btcalibration,info_cmd_value_btcalibration, e.KeyCode, "battery_calibration");
       }

       private void info_cmd_value_calibration_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_calibration,info_cmd_value_calibration, e.KeyCode, "calibration");
       }

       private void info_cmd_value_sensitivity_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_sensitivity,info_cmd_value_sensitivity, e.KeyCode, "sensor_sensitivity");
       }

       private void info_cmd_value_tr_rate_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_tr_rate,info_cmd_value_tr_rate, e.KeyCode, "transmission_mode");
       }


       private void info_cmd_value_sampling_rate_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_sampling_rate,info_cmd_value_sampling_rate, e.KeyCode, "sampling_rate");
       }

       private void info_cmd_value_pwr_timeout_KeyDown(object sender, KeyEventArgs e)
       {
           change_status_field(info_cmd_label_pwr_timeout,info_cmd_value_pwr_timeout, e.KeyCode, "power_down");
       }

       
        #endregion


        #region Buttons

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
                   case "hw_version":
                       info_cmd_value_hwversion.Text = "";
                       Application.DoEvents();
                       cmd = new GET_HV();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "sw_version":
                       info_cmd_value_swversion.Text = "";
                       Application.DoEvents();
                       cmd = new GET_FV();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "packet_count":
                       info_cmd_value_pkt_count.Text = "";
                       Application.DoEvents();
                       cmd = new GET_PC();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_level":
                       info_cmd_value_battery_level.Text = "";
                       Application.DoEvents();
                       cmd = new GET_BT();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_percent":
                       info_cmd_value_btpercent.Text = "";
                       Application.DoEvents();
                       cmd = new GET_BP();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "battery_calibration":
                       info_cmd_value_btcalibration.Text = "";
                       Application.DoEvents();
                       cmd = new GET_BTCAL();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "calibration":
                       info_cmd_value_calibration.Text = "";
                       Application.DoEvents();
                       cmd = new GET_CAL();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "sensor_sensitivity":
                       info_cmd_value_sensitivity.Text = "";
                       Application.DoEvents();
                       cmd = new GET_SEN();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "transmission_mode":
                       info_cmd_value_tr_rate.Text = "";
                       Application.DoEvents();
                       cmd = new GET_TM();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "sampling_rate":
                       info_cmd_value_sampling_rate.Text = "";
                       Application.DoEvents();
                       cmd = new GET_SR();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
                   case "power_down":
                       info_cmd_value_pwr_timeout.Text = "";
                       Application.DoEvents();
                       cmd = new GET_PDT();
                       ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);
                       break;
               }
           }

           button_load.Enabled = true;

       }

       private void button_set_Click(object sender, EventArgs e)
       {

           if (!checkBox_LoadAll.Checked)
           {

               button_set.Enabled = false;

               if (current_command.CompareTo("sensor_sensitivity") == 0)
               {
                   #region Sensitivity

                   string val = info_cmd_value_sensitivity.Text;

                   if (cur_sensitivity.CompareTo(val) != 0)
                   {
                       //sets sensitivity to the selected value
                       // SET_SEN sen = new SET_SEN(val);
                       //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(sen._Bytes);

                       //System.Threading.Thread.Sleep(200);
                   }


                   info_cmd_value_sensitivity.Text = "";
                   Application.DoEvents();
                   System.Threading.Thread.Sleep(200);

                   //reads the sensor sensitivity
                   Command cmd = new GET_SEN();
                   ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

                   #endregion Sensitivity

                   button_set.Enabled = true;
               }
               else if (current_command.CompareTo("transmission_mode") == 0)
               {

                   #region Transmission Mode

                   string trm_val = info_cmd_value_tr_rate.Text;
                   

                   //check if the value changed 
                   if (cur_tr_mode.CompareTo(trm_val) != 0)
                   {
                       //sets the appropriate sampling rate for the new transmission mode
                       int sr_value = cur_sampling_rate;
                       bool is_valid = true;

                       #region Set The Appropriate Sampling Rate

                       if (trm_val.CompareTo("continuous") == 0)
                       {
                           if (cur_sampling_rate < 1 || cur_sampling_rate > 126)
                           {  //set cur_sampling_rate to 90Hz
                               sr_value = 90;
                               is_valid = false;
                           }
                       }
                       else if (trm_val.Contains("30"))
                       {
                           if (cur_sampling_rate < 1 || cur_sampling_rate > 80)
                           {  //set cur_sampling_rate to 80Hz
                               sr_value = 80;
                               is_valid = false;
                           }
                       }
                       else if (trm_val.Contains("60"))
                       {
                           if (cur_sampling_rate < 1 || cur_sampling_rate > 40)
                           {  //set cur_sampling_rate to 40Hz
                               sr_value = 40;
                               is_valid = false;
                           }
                       }
                       else if (trm_val.Contains("90"))
                       {
                           if (cur_sampling_rate < 1 || cur_sampling_rate > 30)
                           {  //set cur_sampling_rate to 30Hz
                               sr_value = 30;
                               is_valid = false;
                           }
                       }
                       else if (trm_val.Contains("120"))
                       {
                           if (cur_sampling_rate < 1 || cur_sampling_rate > 20)
                           {  //set cur_sampling_rate to 20Hz
                               sr_value = 20;
                               is_valid = false;
                           }
                       }


                       #endregion 



                       //if sampling rate is not valid, change to the right value
                       if (!is_valid)
                       {
                           //clean field
                           info_cmd_value_sampling_rate.Text = "";
                           Application.DoEvents();
                           System.Threading.Thread.Sleep(200);

                           //set sampling rate
                           //SET_SR sr = new SET_SR(sr_value);
                           //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(sr._Bytes);

                           //wait for response
                           System.Threading.Thread.Sleep(200);

                           //reads the sampling rate
                           Command sr_cmd = new GET_SR();
                           ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(sr_cmd._Bytes);

                       }


                       //sets transmission mode to the selected value
                       //SET_TM tr = new SET_TM(val);
                       //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(tr._Bytes);

                       //System.Threading.Thread.Sleep(200);
                   }


                   //clean field
                   info_cmd_value_tr_rate.Text = "";
                   Application.DoEvents();

                   //reads the sensor sensitivity
                   Command cmd = new GET_TM();
                   ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);

                   #endregion Transmission Mode

                   button_set.Enabled = true;
               }
               else if (current_command.CompareTo("sampling_rate") == 0)
               {

                   #region Sampling Rate

                   string sr_val = info_cmd_value_sampling_rate.Text;
                   int value = Int32.Parse(sr_val);


                   if (cur_sampling_rate != value)
                   {
                       string tm_val = info_cmd_label_tr_rate.Text;
                       bool is_valid = false;

                       //verify validity
                       if (tm_val.CompareTo("Continous") == 0)
                       {
                           //set_panel_label_status.Text = "The Wockets is set to continous mode. This mode supports sampling rates between 1Hz and 126Hz. Enter the sampling rate in the command textbox.";
                           if (value > 1 && value <= 126)
                               is_valid = true;
                       }
                       else if (tm_val.Contains("30"))
                       {
                           //set_panel_label_status.Text = "The Wockets is set to burst 30 secs mode. This mode supports sampling rates between 1Hz and 80Hz. Enter the sampling rate in the command textbox.";
                           value = Int32.Parse(sr_val);
                           if (value > 1 && value <= 80)
                               is_valid = true;
                       }
                       else if (tm_val.Contains("60"))
                       {
                           //set_panel_label_status.Text = "The Wockets is set to burst 60 secs mode. This mode supports sampling rates between 1Hz and 40Hz. Enter the sampling rate in the command textbox.";
                           value = Int32.Parse(sr_val);
                           if (value > 1 && value <= 40)
                               is_valid = true;
                       }
                       else if (cur_tr_mode.Contains("90"))
                       {
                           //set_panel_label_status.Text = "The Wockets is set to burst 90 secs mode. This mode supports sampling rates between 1Hz and 30Hz. Enter the sampling rate in the command textbox.";
                           value = Int32.Parse(sr_val);
                           if (value > 1 && value <= 30)
                               is_valid = true;
                       }
                       else if (cur_tr_mode.Contains("120"))
                       {
                           //set_panel_label_status.Text = "The Wockets is set to burst 120 secs mode. This mode supports sampling rates between 1Hz and 20Hz. Enter the sampling rate in the command textbox.";
                           value = Int32.Parse(sr_val);
                           if (value > 1 && value <= 20)
                               is_valid = true;
                       }
                       else if (cur_tr_mode.CompareTo("") == 0)
                       {
                           //set_panel_label_status.Text = "Before setting up the sampling rate, it is necessary specify the transmission mode.";
                       }


                       //sets the sampling rate to the selected value
                       if (is_valid)
                       {
                           SET_SR sr = new SET_SR(value);
                           ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(sr._Bytes);
                       }
                   }


                   //clean field
                   info_cmd_value_sampling_rate.Text = "";
                   Application.DoEvents();
                   System.Threading.Thread.Sleep(200);

                   //reads the sampling rate
                   Command cmd = new GET_SR();
                   ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);


                   #endregion Sampling Rate

                   button_set.Enabled = true;
               }
               else if (current_command.CompareTo("power_down") == 0)
               {

                   #region PowerDown Timeout

                   string pdt_val = info_cmd_value_pwr_timeout.Text;


                   if (pdt_val.Trim().CompareTo("") != 0)
                   {
                       try
                       {
                           int value = Int32.Parse(pdt_val);

                           if (cur_power_down != value)
                           {
                               //verify validity
                               if (value >= 1 && value <= 127)
                               {   //set the power down timeout  according the permitted range in minutes
                                   SET_PDT pdt = new SET_PDT(value);
                                   ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(pdt._Bytes);
                               }
                               else
                               {
                                   //set_panel_label_status.Text = "The time you entered is out of range. The power down timeout range is between 1 min and 127 minutes.";       
                               }
                           }
                       }
                       catch
                       {
                           //TODO
                           //set_panel_label_status.Text = "The time you entered is out of range. The power down timeout range is between 1 min and 127 minutes.";       
                       }
                   }


                   //clean field
                   info_cmd_value_pwr_timeout.Text = "";
                   Application.DoEvents();
                   System.Threading.Thread.Sleep(200);

                   //reads the power down timeout
                   Command cmd = new GET_PDT();
                   ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);


                   #endregion PowerDown Timeout

                   button_set.Enabled = true;
               }
               else if (current_command.CompareTo("calibration") == 0)
               {
                   #region Calibration

                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_calibration.Text;
                   cal_panel_cmd_label.Text = "File";
                   cal_panel_entry_path.Text = "";
                   cal_panel_label_status.Text = "";

                   panel_status_texbox.Text = "";
                   panel_status.Visible = false;

                   cal_panel_values_BTpercent.Visible = false;
                   cal_panel_cal_values.Visible = true;

                   panel_calibration.Visible = true;
                   is_sensordata_valid = false;

                   #endregion Calibration

               }
               else if (current_command.CompareTo("battery_calibration") == 0)
               {
                   #region BAT Calibration
                   //setup the calibration panel parameters
                   cal_panel_title.Text = info_cmd_label_btcalibration.Text;
                   cal_panel_cmd_label.Text = "File";
                   cal_panel_entry_path.Text = "";
                   cal_panel_label_status.Text = "";

                   panel_status_texbox.Text = "";
                   panel_status.Visible = false;

                   cal_panel_values_BTpercent.Visible = true;
                   cal_panel_cal_values.Visible = false;

                   panel_calibration.Visible = true;
                   is_sensordata_valid = false;

                   #endregion BAT Calibration

               }
               else
               {
                   button_set.Enabled = true;
               }

           }
       }

        
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

        private void cal_panel_button_ok_Click(object sender, EventArgs e)
        {

          
            // if sensor data file is valid 
            if (is_sensordata_valid)
            {
                
                if (current_command.CompareTo("calibration") == 0)
                {
                    // set the calibration parameters
                    // SET_CAL setcal = new SET_CAL();
                    //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(setcal._Bytes);

                    //clean field
                    info_cmd_value_calibration.Text = "";
                    Application.DoEvents();
                    //System.Threading.Thread.Sleep(200);


                    // get the calibration parameters
                    GET_CAL cal = new GET_CAL();
                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cal._Bytes);
                }
                else if( current_command.CompareTo("battery_calibration") == 0)
                {
                    // set the battery calibration parameters
                    // SET_BTCAL btcal = new SET_BTCAL();
                    //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(btcal._Bytes);

                    //clean field
                    info_cmd_value_btcalibration.Text = "";
                    Application.DoEvents();
                    System.Threading.Thread.Sleep(200);


                    // get the calibration parameters
                    GET_BTCAL btcal = new GET_BTCAL();
                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(btcal._Bytes);
                }

                //restore status panel
                restore_status_panel();

            }
            else
            {
                if(current_command.CompareTo("calibration") == 0)
                    cal_panel_label_status.Text = "The path for the sensordata file is not valid. Please enter a valid file or click CANCEL to exit.";
                else if(current_command.CompareTo("battery_calibration") == 0)
                    cal_panel_label_status.Text = "The path for the battery calibration file is not valid. Please enter a valid file or click CANCEL to exit.";
             
            }
 
        }

        private void cal_panel_button_cancel_Click(object sender, EventArgs e)
        {
            //restore status panel
            restore_status_panel();
        }

        private void cal_panel_button_browse_Click(object sender, EventArgs e)
        {
              try
              {
                  //check the path selected in the textbox
                  //this.folderBrowserDialog1.ShowNewFolderButton = false;
                  this.openFileDialog1.Multiselect = false;
                  this.openFileDialog1.FileName = "*.xml";
                  


                  if (cal_panel_entry_path.Text.Trim().CompareTo("") != 0)
                  {
                      if (Directory.Exists(cal_panel_entry_path.Text))
                      { //this.folderBrowserDialog1.SelectedPath = cal_panel_entry_path.Text.ToString();
                          this.openFileDialog1.InitialDirectory = cal_panel_entry_path.Text.ToString();
                      }
                      //else
                      //{ //this.folderBrowserDialog1.RootFolder = System.Environment.SpecialFolder.Desktop; 
                      //    this.openFileDialog1.InitialDirectory = System.Environment.SpecialFolder.Desktop.ToString(); 
                      //}
                  }
                  //else
                  //{
                  //    //this.folderBrowserDialog1.RootFolder = System.Environment.SpecialFolder.Desktop;
                  //    this.openFileDialog1.InitialDirectory = System.Environment.SpecialFolder.Desktop.ToString();
                  //}


                  //check the path selected in the dialog
                 // DialogResult result = this.folderBrowserDialog1.ShowDialog();
                  DialogResult result = this.openFileDialog1.ShowDialog();


                  if (result == DialogResult.OK)
                  {
                      //string fullPath = this.folderBrowserDialog1.SelectedPath;
                      string fullPath = this.openFileDialog1.FileName;

                      cal_panel_entry_path.Text = fullPath;

                      if (cal_panel_entry_path.Text.Trim().CompareTo("") == 0)
                      {
                          cal_panel_label_status.Text = "Please provide a valid path";
                      }
                      else
                      {

                          WocketsController wc_xml = new WocketsController("", "", "");
                          wc_xml.FromXML(fullPath);
                          Accelerometer acc_sensor = (Accelerometer)wc_xml._Sensors[0];
                          
                          
                          //if it is a valid sensordata file with calibration values
                          //open the sensordata file and get the calibration values 
                          //fullPath = fullPath + "\\SensorData.xml";
                          if (File.Exists(fullPath))
                          {

                              if (current_command.CompareTo("calibration") == 0)
                              {
                                  //update the calibration fields
                                  cal_panel_x1g.Text = acc_sensor._X1g.ToString();
                                  cal_panel_xn1g.Text = acc_sensor._Xn1g.ToString();
                                  cal_panel_xstd.Text = acc_sensor._XStd.ToString();

                                  cal_panel_y1g.Text = acc_sensor._Y1g.ToString();
                                  cal_panel_yn1g.Text = acc_sensor._Yn1g.ToString();
                                  cal_panel_ystd.Text = acc_sensor._YStd.ToString();

                                  cal_panel_z1g.Text = acc_sensor._Z1g.ToString();
                                  cal_panel_zn1g.Text = acc_sensor._Zn1g.ToString();
                                  cal_panel_zstd.Text = acc_sensor._ZStd.ToString();

                                  //load the fields
                                  xyzP[0] = acc_sensor._X1g;
                                  xyzP[1] = acc_sensor._Y1g;
                                  xyzP[2] = acc_sensor._Z1g;

                                  xyzN[0] = acc_sensor._Xn1g;
                                  xyzN[1] = acc_sensor._Yn1g;
                                  xyzN[2] = acc_sensor._Zn1g;

                                  xyzSTD[0] = acc_sensor._XStd;
                                  xyzSTD[1] = acc_sensor._YStd;
                                  xyzSTD[2] = acc_sensor._ZStd;


                                  //write the status to screen
                                  cal_panel_label_status.Text = "The sensordata file is valid. You can set the CAL values.";
                                  is_sensordata_valid = true;

                              }
                              else if (current_command.CompareTo("battery_calibration") == 0)
                              {
                                  // it is a valid sensordata file with calibration values
                                  //open the battery calibration file and get the cal values   
                                  cal_panel_label_status.Text = "The battery calibration file is valid. You can set the CAL values.";
                                  is_sensordata_valid = true;
                              }
                          }
                          else
                          {
                              cal_panel_label_status.Text = "The sensordata file is NOT valid. Please try again or click CANCEL to exit the calibration.";
                          }

                          //dispose xml wockets controller
                          acc_sensor.Dispose();
                          wc_xml.Dispose();

                      }
                  }

              } // end try
              catch (Exception err)
              {
                  Console.WriteLine(err.Message);
              }


        }


        private void restore_status_panel()
        {

            //Restore status panel
            panel_status_texbox.Text = "";
            panel_status.Visible = true;

            //clean calibration panel
            cal_panel_title.Text = "";
            cal_panel_cmd_label.Text = "";
            cal_panel_entry_path.Text = "";

            clean_calibration_values();

            cal_panel_values_BTpercent.Visible = false;
            cal_panel_cal_values.Visible = false;

            panel_calibration.Visible = false;

            //reset variables
            is_sensordata_valid = false;
            button_set.Enabled = true;

        }

        private void clean_calibration_values()
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

            //load the fields
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

       
       #endregion Buttons


        //Close Forms 
        #region Close Forms

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
        }

        #endregion


    }//end form
}//end namespace