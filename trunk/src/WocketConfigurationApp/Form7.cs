using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
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


namespace WocketConfigurationApp
{
    public partial class Form7 : Form
    {
        BluetoothDeviceInfo wocket;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        WocketsController wc;

        private string latestReading;

        private string current_command = "";
        private string cur_tr_mode = "";


        #region Initialize

        public Form7(BluetoothDeviceInfo wocket)
        {
            InitializeComponent();
            
            //Copy parameters to loacal variables
            this.wocket = wocket;
            this.info_cmd_value_name.Text = wocket.DeviceName;
            this.info_cmd_value_mac.Text = wocket.DeviceAddress.ToString();
            this.Text = "Wocket (" + wocket.DeviceAddress.ToString() + ")";

        }


        private void Form2_Load(object sender, EventArgs e)
        {
            InitializeWocketParameters();

            panel_calibration.Visible = false;
            panel_set_container.Visible = false;
            set_panel_cmd_entry_combo.Visible = false;
            set_panel_cmd_entry_textbox.Visible = false;
            

        }



        private void InitializeWocketParameters()
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
            wc._Decoders[0].Subscribe(Wockets.Data.SensorDataType.COMMAND_MODE_ENTERED, new Response.ResponseHandler(this.CommandCallback));
            wc._Decoders[0].Subscribe(Wockets.Data.SensorDataType.BAUD_RATE, new Response.ResponseHandler(this.CommandCallback));
            wc.Initialize();

        }



        #endregion Initialize




        #region Delegates Callback

        delegate void UpdateCommandCallback(object sender, Wockets.Decoders.Response.ResponseArgs e);

        private void CommandCallback(object sender, Wockets.Decoders.Response.ResponseArgs e)
        {
            if (this.InvokeRequired)
            {
                UpdateCommandCallback d = new UpdateCommandCallback(CommandCallback);
                this.Invoke(d, new object[] { sender, e });
            }
            else
            {
                if (e._Response.Type == Wockets.Data.SensorDataType.COMMAND_MODE_ENTERED)
                {
                    CurrentWockets._Controller._Sensors[0]._Mode = SensorModes.Command;
                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(new byte[3] { 13, 13, 13 });
                    this.label27.Text = "Connected: Command Mode";

                }
                else if (e._Response.Type == Wockets.Data.SensorDataType.BAUD_RATE)
                {
                    if (((Wockets.Data.Responses.BaudRateResponse)e._Response)._BaudRate == "38.4")
                        this.set_panel_cmd_entry_combo.SelectedIndex = 5;
                }
                this.Refresh();
            }
        }


        #endregion


        #region Reconnect & Timer


        private void timer1_Tick(object sender, EventArgs e)
        {

            if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Disconnected)
                this.label27.Text = "Disconnected";
            else if (CurrentWockets._Controller._Receivers[0]._Status == ReceiverStatus.Reconnecting)
                this.label27.Text = "Reconnecting";
            else
            {

                if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Data)
                    this.label27.Text = "Connected: Data Mode";
                else
                    this.label27.Text = "Connected: Command Mode";
            }

        }

        #endregion


        #region old code
        private void comboBox1_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Command)
            {
                Command c = new GET_BR();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(c._Bytes);
            }
        }

        private void commandToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Data)
            {
                ((RFCOMMReceiver)wc._Receivers[0])._TimeoutEnabled = false;
                CurrentWockets._Controller._Decoders[0]._Mode = DecoderModes.Command;
                Command c = new EnterCommandMode();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(c._Bytes);
            }
        }

        private void dataToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (CurrentWockets._Controller._Sensors[0]._Mode == SensorModes.Command)
            {
                CurrentWockets._Controller._Decoders[0]._Mode = DecoderModes.Data;
                Command c = new ExitCommandMode();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(c._Bytes);
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


       
        

        

        private void button_finish_Click(object sender, EventArgs e)
        {
            this.Close();

        }


        private void set_panel_button_close_Click(object sender, EventArgs e)
        {
            if (current_command.CompareTo("name") == 0)
            {
                set_panel_cmd_entry_textbox.Text = "";
                set_panel_cmd_entry_textbox.Visible = false;
                info_button_name.Enabled = true;
            }
            else if (current_command.CompareTo("sensitivity") == 0)
            {
                set_panel_cmd_entry_combo.Visible = false;
                info_button_sensitivity.Enabled = true;
            }
            else if (current_command.CompareTo("tr_mode") == 0)
            {
                set_panel_cmd_entry_combo.Visible = false;
                info_button_tr_rate.Enabled= true;
            }
            else if (current_command.CompareTo("sampling_rate") == 0)
            {
                set_panel_cmd_entry_textbox.Text = "";
                set_panel_cmd_entry_textbox.Visible = false;
                info_button_sampling_rate.Enabled = true;
            }
            else if (current_command.CompareTo("pwr_timeout") == 0)
            {
                set_panel_cmd_entry_textbox.Text = "";
                set_panel_cmd_entry_textbox.Visible = false;
                info_button_pwr_timeout.Enabled = true;
            }

            current_command = "";
            
            panel_set_container.Visible = false;
            set_panel_label_status.Text = "";
            set_panel_cmd_label.Text = "";
            set_panel_title.Text= "";

        }



        //Click the "set" button in the configuration panel
        private void set_panel_button_set_Click(object sender, EventArgs e)
        {
            try
            {
                set_panel_button_set.Enabled = false;
                Application.DoEvents();

                if (current_command.CompareTo("name") == 0)
                {
                   
                    //set the name that the user entered in the set textbox 
                    info_cmd_value_name.Text = set_panel_cmd_entry_textbox.Text;
                   
                }
                else if (current_command.CompareTo("sensitivity") == 0)
                {
                    info_button_sensitivity.Enabled = false;
                    Application.DoEvents();

                   int index = set_panel_cmd_entry_combo.SelectedIndex;
                   string strval = set_panel_cmd_entry_combo.Items[index].ToString();


                    //set the sensitivity level selected in the combo box
                   if (index > 0)
                   {
                       //string value = strval.Split(' ')[0];
                       info_cmd_value_sensitivity.Text = strval;
                       info_button_sensitivity.Enabled = true;
                       set_panel_label_status.Text = "";
                   }
                   else
                   {
                       set_panel_label_status.Text = "Select a valid entry from the pull down menu.";
                   }
                    
                }
                else if (current_command.CompareTo("tr_mode") == 0)
                {
                    int index = set_panel_cmd_entry_combo.SelectedIndex;
                    string strval = set_panel_cmd_entry_combo.Items[index].ToString();
                    
                    //set the transmission mode selected in the combo box
                    if (index > 0)
                    {
                        if (strval.CompareTo("Continuous") == 0)
                        {
                            //set the wockets to transmit in countinous mode
                            cur_tr_mode = "continous";
                        }
                        else
                        {
                            string burst_value = strval.Split(' ')[2];
                            //set the wockets to transmit in countinous mode
                            cur_tr_mode = burst_value;
                        }


                        info_cmd_value_tr_rate.Text = strval;
                        set_panel_label_status.Text = "";
                    }
                    else
                    {
                        set_panel_label_status.Text = "Select a valid entry from the pull down menu.";
                    }

                }
                else if (current_command.CompareTo("sampling_rate") == 0)
                {
                    bool outOfrange = false;
                    int val = 0;

                    //get the sampling rate
                    if (set_panel_cmd_entry_textbox.Text.Trim().CompareTo("") != 0)
                        val = Int32.Parse(set_panel_cmd_entry_textbox.Text);


                    //set the sampling rate according with the transmission mode
                    if (cur_tr_mode.CompareTo("continuous") == 0)
                    {
                        if (val >= 1 && val <= 126)
                        {
                            //set the wockets sampling rate in countinous mode
                            info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
                        }
                        else
                            outOfrange = true;
                    }
                    else if (cur_tr_mode.CompareTo("30") == 0)
                    {
                        if (val >= 1 && val <= 80)
                        {
                            //set the wockets sampling rate in burst 30 secs mode
                            info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
                        }
                        else
                            outOfrange = true;
                    }
                    else if (cur_tr_mode.CompareTo("60") == 0)
                    {
                        if (val >= 1 && val <= 40)
                        {
                            //set the wockets sampling rate in burst 60 secs mode
                            info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
                        }
                        else
                            outOfrange = true;
                    }
                    else if (cur_tr_mode.CompareTo("90") == 0)
                    {
                        if (val >= 1 && val <= 30)
                        {
                            //set the wockets sampling rate in burst 90 secs mode
                            info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
                        }
                        else
                            outOfrange = true;
                    }
                    else if (cur_tr_mode.CompareTo("120") == 0)
                    {
                        if (val >= 1 && val <= 20)
                        {
                            //set the wockets sampling rate in burst 90 secs mode
                            info_cmd_value_sampling_rate.Text = val.ToString() + " Hz";
                        }
                        else
                            outOfrange = true;
                    }



                    if (outOfrange == true)
                    {
                        set_panel_label_status.Text = set_panel_label_status.Text + "\n\r Sampling rate out of range.";
                        info_cmd_value_sampling_rate.Text = "out of range";
                    }
                }
                else if (current_command.CompareTo("pwr_timeout") == 0)
                {
                    bool outOfrange = false;
                    int val = 0;

                    //get the sampling rate
                    if (set_panel_cmd_entry_textbox.Text.Trim().CompareTo("") != 0)
                        val = Int32.Parse(set_panel_cmd_entry_textbox.Text);


                    //set the power down timeout  according the permitted range in minutes
                    if (val >= 1 && val <= 127)
                    {
                        //set the wockets sampling rate in countinous mode
                        info_cmd_value_pwr_timeout.Text = val.ToString() + " Hz";
                    }
                    else
                    {
                        set_panel_label_status.Text = "The time you entered is out of range. /n/r The power down timeout range is between 1 min and 127 minutes.";
                        info_cmd_value_pwr_timeout.Text = "out of range";
                    }
                }
                    

                set_panel_button_set.Enabled = true;
                
            }
            catch
            {
                set_panel_button_set.Enabled = true;

                if (set_panel_cmd_entry_combo.Visible == true)
                    set_panel_cmd_entry_combo.SelectedIndex = 0;
                else if (set_panel_cmd_entry_textbox.Visible == true)
                    set_panel_cmd_entry_textbox.Text = "";


            }
        }


        private void button_set_name_Click(object sender, EventArgs e)
        {
            
            current_command = "name";

            set_panel_title.Text = info_cmd_label_name.Text;
            set_panel_cmd_label.Text = info_cmd_label_name.Text;
            set_panel_cmd_entry_textbox.Text = info_cmd_value_name.Text;

            set_panel_cmd_entry_textbox.Visible = true;
            set_panel_cmd_entry_combo.Visible = false;

            panel_set_container.Visible = true;
            info_button_name.Enabled = false;

        }

        private void button_load_hw_version_Click(object sender, EventArgs e)
        {
            current_command = "hw_version";

            try
            {
                info_button_hwversion.Enabled = false;
                Application.DoEvents();

                //querry the hw version 
                //set the hw version
                info_cmd_value_hwversion.Text = "Rev. 3";

                info_button_hwversion.Enabled = true;

            }
            catch
            {
                // error
                info_cmd_value_hwversion.Text = "Error, version not loaded.";
                info_button_hwversion.Enabled = true;
            }

            current_command = "";
        }

        private void info_button_swversion_Click(object sender, EventArgs e)
        {
            current_command = "sw_version";

            try
            {
                info_button_swversion.Enabled = false;
                Application.DoEvents();

                //querry the sw version 
                //set the sw version
                info_cmd_value_swversion.Text = "Rev. 3";

                info_button_swversion.Enabled = true;

            }
            catch
            {
                // error
                info_cmd_value_swversion.Text = "Error, version not loaded.";
                info_button_swversion.Enabled = true;
            }

            current_command = "";
        }


        private void button_load_battery_level_Click(object sender, EventArgs e)
        {
            current_command = "battery";

            try
            {
                info_button_battery_level.Enabled= false;
                Application.DoEvents();

                //querry the battery level 
                //set the battery level
                info_cmd_value_battery_level.Text = "100%";

                info_button_battery_level.Enabled = true;

            }
            catch
            {
                // error
                info_cmd_value_battery_level.Text = "Error.Battery level not loaded.";
                info_button_battery_level.Enabled = true;
            }

            current_command = "";
        }

        private void button_load_calibration_Click(object sender, EventArgs e)
        {

        }


        private void button_set_sensitivity_Click(object sender, EventArgs e)
        {
            current_command = "sensitivity";

            //add sensitivity options to combo box
            set_panel_cmd_entry_combo.Items.Clear();
            set_panel_cmd_entry_combo.Items.Add("");
            set_panel_cmd_entry_combo.Items.Add("1.5 g");
            set_panel_cmd_entry_combo.Items.Add("2.0 g");
            set_panel_cmd_entry_combo.Items.Add("4.0 g");
            set_panel_cmd_entry_combo.Items.Add("6.0 g");


            //prepare the set panel
            set_panel_title.Text = info_cmd_label_sensitivity.Text;
            set_panel_cmd_label.Text = info_cmd_label_sensitivity.Text;
            set_panel_cmd_entry_combo.SelectedIndex = 0;
            set_panel_label_status.Text = "";

            set_panel_cmd_entry_combo.Visible = true;
            set_panel_cmd_entry_textbox.Visible = false;

            panel_set_container.Visible = true;
            info_button_sensitivity.Enabled = false;

        }


        private void info_button_tr_rate_Click(object sender, EventArgs e)
        {
            current_command = "tr_mode";

            //add sensitivity options to combo box
            set_panel_cmd_entry_combo.Items.Clear();
            set_panel_cmd_entry_combo.Items.Add("");
            set_panel_cmd_entry_combo.Items.Add("Continuous");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 30 secs");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 60 secs");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 90 secs");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 120 secs");

            //prepare the set panel
            set_panel_title.Text = info_cmd_label_tr_rate.Text;
            set_panel_cmd_label.Text = info_cmd_label_tr_rate.Text;
            set_panel_cmd_entry_combo.SelectedIndex = 0;
            set_panel_label_status.Text = "";

            set_panel_cmd_entry_combo.Visible = true;
            set_panel_cmd_entry_textbox.Visible = false;

            panel_set_container.Visible = true;
            info_button_tr_rate.Enabled = false;

        }


        private void info_button_sampling_rate_Click(object sender, EventArgs e)
        {
            current_command = "sampling_rate";

            //select the allowed sampling rate
            if (cur_tr_mode.CompareTo("continous") == 0)
            {
                set_panel_label_status.Text = "The Wockets is set to continous mode. \n\r This mode supports sampling rates between 1Hz and 126Hz. \n\r Enter the sampling rate in the command textbox.";
            }
            else if (cur_tr_mode.CompareTo("30") == 0)
            {
                set_panel_label_status.Text = "The Wockets is set to burst 30 secs mode. \n\r This mode supports sampling rates between 1Hz and 80Hz. \n\r Enter the sampling rate in the command textbox.";
            }
            else if (cur_tr_mode.CompareTo("60") == 0)
            {
                set_panel_label_status.Text = "The Wockets is set to burst 60 secs mode. \n\r This mode supports sampling rates between 1Hz and 40Hz. \n\r Enter the sampling rate in the command textbox.";
            }
            else if (cur_tr_mode.CompareTo("90") == 0)
            {
                set_panel_label_status.Text = "The Wockets is set to burst 90 secs mode. \n\r This mode supports sampling rates between 1Hz and 30Hz. \n\r Enter the sampling rate in the command textbox.";
            }
            else if (cur_tr_mode.CompareTo("120") == 0)
            {
                set_panel_label_status.Text = "The Wockets is set to burst 120 secs mode. \n\r This mode supports sampling rates between 1Hz and 20Hz. \n\r Enter the sampling rate in the command textbox.";
            }
            else if (cur_tr_mode.CompareTo("") == 0)
            {
                set_panel_label_status.Text = "Before setting up the sampling rate, it is necessary specify the transmission mode.";

                set_panel_button_set.Enabled = false;
                set_panel_cmd_entry_textbox.Enabled = false;
            }


            //prepare the set panel
            set_panel_title.Text = info_cmd_label_sampling_rate.Text;
            set_panel_cmd_label.Text = info_cmd_label_sampling_rate.Text;
            set_panel_cmd_entry_textbox.Text = "";

            set_panel_cmd_entry_combo.Visible = false;
            set_panel_cmd_entry_textbox.Visible = true;
            panel_set_container.Visible = true;
            info_button_sampling_rate.Enabled= false;

        }

        private void info_button_pwr_timeout_Click(object sender, EventArgs e)
        {
            current_command = "pwr_timeout";

            //prepare the set panel
            set_panel_title.Text = info_cmd_label_pwr_timeout.Text;
            set_panel_cmd_label.Text = info_cmd_label_pwr_timeout.Text;
            set_panel_cmd_entry_textbox.Text = "";

            set_panel_cmd_entry_combo.Visible = false;
            set_panel_cmd_entry_textbox.Visible = true;
            panel_set_container.Visible = true;
            info_button_pwr_timeout.Visible= false;

        }

        private void button_load_baudrate_Click(object sender, EventArgs e)
        {
            current_command = "baudrate";


            try
            {
                info_button_baudrate.Enabled= false;
                Application.DoEvents();

                //querry the hw version 
                //set the hw version
                info_cmd_value_baudrate.Text = "38.4";

                info_button_baudrate.Enabled = true;

            }
            catch
            {
                // error
                info_cmd_value_baudrate.Text = "Error. Baudrate not loaded.";
                info_button_baudrate.Enabled = true;
            }

            current_command = "";

        }

        

        


        



       




    }//end form
}//end namespace