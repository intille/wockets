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
        BluetoothDeviceInfo wocket;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        WocketsController wc;

        private string latestReading;
        private string current_command = "";
        private string cur_tr_mode = "";

        private int[] xyzP = new int[3] {512,512,512};
        private int[] xyzN = new int[3] { -512, -512, -512 };


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
            
            //hw & sw versions 
            //(needs to be updated when they are implemented in the firmware)
            this.info_cmd_value_hwversion.Text = "Version SD-3";
            this.info_cmd_value_swversion.Text = "Rev. 3";

            //battery level
            //calibration
            //sensor sensitivity
            //transmission mode/sampling rate
            //power down timeout / alive timeout
            //packet count/ rssi


        }


        private void Form2_Load(object sender, EventArgs e)
        {
            InitializeWocketParameters();


            //Hide the setting panels
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


            //=== Suscriptions ===

            //packet count
            wc._Decoders[0].Subscribe(ResponseTypes.PC_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            
            //battery level
            wc._Decoders[0].Subscribe(ResponseTypes.BL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            
            //battery percent
            wc._Decoders[0].Subscribe(ResponseTypes.BP_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            
            //battery calibration?

            //calibration
            wc._Decoders[0].Subscribe(ResponseTypes.CAL_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
           
            //sensor sensitivity
            wc._Decoders[0].Subscribe(ResponseTypes.SENS_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            
            //sampling rate
            wc._Decoders[0].Subscribe(ResponseTypes.SR_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            
            //transmission mode
            wc._Decoders[0].Subscribe(ResponseTypes.TM_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            

            //power down timeout 
            wc._Decoders[0].Subscribe(ResponseTypes.PDT_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));
            
            // alive timeout
            wc._Decoders[0].Subscribe(ResponseTypes.ALT_RSP, new Wockets.Decoders.Decoder.ResponseHandler(this.ResponseCallback));


           

            //=== Initialize === 
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
                this.Invoke(d, new object[] {e});
            }
            else 
            {
               Response response = (Wockets.Data.Responses.Response) e;
               switch (response._Type)
               {
                   //packet count
                   case ResponseTypes.PC_RSP:
                       //info_cmd_value_pkt_count.Text = ((PC_RSP)response);
                       break;

                   //battery level
                   case ResponseTypes.BL_RSP:
                       info_cmd_value_battery_level.Text = ((BL_RSP)response)._BatteryLevel.ToString();
                       break;
                   //battery percent
                   case ResponseTypes.BP_RSP:
                       info_cmd_value_btpercent.Text = ((BP_RSP)response)._Percent.ToString();
                       break;

                   //battery calibration?

                   //calibration
                   case ResponseTypes.CAL_RSP:
                       info_cmd_value_calibration.Text = "X:" + ((CAL_RSP)response)._X1G + "-" + ((CAL_RSP)response)._XN1G +
                                                       ", Y:" + ((CAL_RSP)response)._Y1G + "-" + ((CAL_RSP)response)._YN1G +
                                                       ", Z:" + ((CAL_RSP)response)._Z1G + "-" + ((CAL_RSP)response)._ZN1G;
                       
                       xyzP[0] = ((CAL_RSP)response)._X1G;
                       xyzP[1] = ((CAL_RSP)response)._Y1G;
                       xyzP[2] = ((CAL_RSP)response)._Z1G;

                       xyzN[0] = ((CAL_RSP)response)._XN1G;
                       xyzN[1] = ((CAL_RSP)response)._YN1G;
                       xyzN[2] = ((CAL_RSP)response)._ZN1G;
                                
                       break;

                   //sensor sensitivity
                   case ResponseTypes.SENS_RSP:
                       //info_cmd_value_sensitivity.Text = ((SENS_RSP)response);
                       break;
                   //transmission mode
                   case ResponseTypes.TM_RSP:
                       info_cmd_value_tr_rate.Text = ((TM_RSP)response)._TransmissionMode.ToString();
                       break;
                   //sampling rate
                   case ResponseTypes.SR_RSP:
                       info_cmd_value_sampling_rate.Text = ((SR_RSP)response)._SamplingRate.ToString();
                       break;
                   //power down timeout
                   case ResponseTypes.PDT_RSP:
                       //info_cmd_value_pwr_timeout.Text = ((PDT_RSP)response);
                       break;
                   //alive timeout
                   case ResponseTypes.ALT_RSP:
                       //info_cmd_value_alive.Text = ((ALT_RSP)response);
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


       
        

        

        private void button_finish_Click(object sender, EventArgs e)
        {
            close_form();
            this.Close();
        }


        //------  Close & CleanUp panel   --------
        #region Close & Clean up panels
        
        private void set_panel_button_close_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();
        }

        private void set_panel_cleanup()
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
                info_button_tr_rate.Enabled = true;
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
            else if (current_command.CompareTo("calibration") == 0)
            {
                cal_panel_entry_path.Text = "";
                cal_panel_entry_path.Visible= false;
                info_button_calibration.Enabled = true;

                panel_calibration.Visible = false;
                cal_panel_label_status.Text = "";
                cal_panel_cmd_label.Text = "";
                cal_panel_title.Text = "";

            }
            else if (current_command.CompareTo("alive") == 0)
            {
                set_panel_cmd_entry_textbox.Text = "";
                set_panel_cmd_entry_textbox.Visible = false;
                info_button_alive.Enabled = true;
            }


            current_command = "";

            panel_set_container.Visible = false;
            set_panel_label_status.Text = "";
            set_panel_cmd_label.Text = "";
            set_panel_title.Text = "";

        }

        private void set_panel_setup(string title, string label, string value, bool text_on) 
        {

            set_panel_title.Text = title;
            set_panel_cmd_label.Text = label;
           


            if (text_on)
            {
                set_panel_cmd_entry_textbox.Text = value;

                set_panel_cmd_entry_textbox.Visible = true;
                set_panel_cmd_entry_textbox.Enabled = true;

                set_panel_cmd_entry_combo.Visible = false;
                set_panel_cmd_entry_combo.Enabled = false;
            }
            else
            {

                set_panel_cmd_entry_textbox.Visible = false;
                set_panel_cmd_entry_textbox.Enabled = false;

                set_panel_cmd_entry_combo.Visible = true;
                set_panel_cmd_entry_combo.Enabled = true;
            }

            set_panel_button_set.Enabled = true;
            set_panel_button_close.Enabled = true;

            panel_set_container.Visible = true;
        
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
                else if (current_command.CompareTo("alive") == 0)
                {
                    bool outOfrange = false;
                    int val = 0;

                    //get the alive timeout
                    if (set_panel_cmd_entry_textbox.Text.Trim().CompareTo("") != 0)
                        val = Int32.Parse(set_panel_cmd_entry_textbox.Text);


                    //set the alive timeout  according the permitted range in seconds
                    if (val >= 10)
                    {
                        //set the alive timeout in seconds
                        info_cmd_value_alive.Text = val.ToString() + " Secs";
                    }
                    else
                    {
                        set_panel_label_status.Text = "The time you entered is too short. /n/r The alive timeout minimum value is 10 seconds.";
                        info_cmd_value_alive.Text = "?";
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
        


        #endregion 


        //-------  Commands -----------------------
        #region commands

        //name
        private void button_set_name_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();
            current_command = "name";

            set_panel_setup(info_cmd_label_name.Text, info_cmd_label_name.Text, info_cmd_value_name.Text, true);

            info_button_name.Enabled = false;

        }

        //hardware version
        private void button_load_hw_version_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

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

        //software version
        private void info_button_swversion_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

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


        //packet count
        private void info_button_pkt_count_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "packet_count";

            try
            {
                info_button_pkt_count.Enabled = false;
                Application.DoEvents();

                //get the packets count
                info_cmd_value_pkt_count.Text = get_packet_count();

                info_button_pkt_count.Enabled = true;

            }
            catch
            {
                // error
                info_cmd_value_pkt_count.Text = "Error.Packet count not loaded.";
                info_button_pkt_count.Enabled = true;
            }

            current_command = "";
        }

        private string get_packet_count()
        {
            string val = "?";

            try
            {
                //GET_PC pc = new GET_PC();
                //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(pc._Bytes);
                //val = pc._Bytes[0].ToString();
            }
            catch
            {
                val = "?";
            }

            return val;
        }


        //battery level
        private void button_load_battery_level_Click(object sender, EventArgs e)
        {

            set_panel_cleanup();

            current_command = "battery";

            try
            {
                info_button_battery_level.Enabled= false;
                Application.DoEvents();

                //querry the battery level 
                //set the battery level
                info_cmd_value_battery_level.Text = get_battery_level();

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

        private string get_battery_level()
        {
            string val = "?";

            try
            {
                //GET_BT bt_level = new GET_BT();
                //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(bt_level._Bytes);
                //val = bt_level._Bytes.ToString();
            }
            catch 
            {
                val = "?";
            }

            return val;
        }


        //calibration
        private void button_load_calibration_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "calibration";
            info_cmd_value_calibration.Text = get_sensor_calibration();

            //prepare the calibration panel
            cal_panel_title.Text = info_cmd_label_calibration.Text;
            cal_panel_cmd_label.Text = info_cmd_label_calibration.Text;
            cal_panel_entry_path.Text = "";
            cal_panel_label_status.Text = "";

            cal_panel_entry_path.Visible = true;
            panel_calibration.Visible = true;
            
            info_button_calibration.Enabled = false;

        }

        private string get_sensor_calibration()
        {
            string val = "?";

            try
            {
                //GET_CAL cal = new GET_CAL();
                //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cal._Bytes);
               // val = cal._Bytes.ToString();
            }
            catch
            {
                val = "?";
            }

            return val;
        }
        
        //calibration  panel buttons
        private void cal_panel_button_browse_Click(object sender, EventArgs e)
        {
            try
            {
                //check the path selected in the textbox
                this.folderBrowserDialog1.ShowNewFolderButton = false;

                if (cal_panel_entry_path.Text.Trim().CompareTo("") != 0)
                {
                    if (Directory.Exists(cal_panel_entry_path.Text))
                    { this.folderBrowserDialog1.SelectedPath = cal_panel_entry_path.Text.ToString(); }
                    else
                    { this.folderBrowserDialog1.RootFolder = System.Environment.SpecialFolder.Desktop; }
                }
                else
                {
                    this.folderBrowserDialog1.RootFolder = System.Environment.SpecialFolder.Desktop;
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
                        // it is a valid file
                        //open the sensordata file and get the calibration values   
                        cal_panel_label_status.Text = "The sensordata file is valid. You can set the CAL values.";
                    }
                }


            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }
        }

        private void cal_panel_button_set_Click(object sender, EventArgs e)
        {

            cal_panel_button_set.Enabled = false;

            if (cal_panel_entry_path.Text.Trim().CompareTo("") == 0)
            {
                cal_panel_label_status.Text = "Please provide a valid path";
            }
            else
            {
                // if is a valid path
                // check if it is a valid file
                // open the file and get the calibration values

                //set status
                cal_panel_label_status.Text = "The CAL values were set.";
            }

            cal_panel_button_set.Enabled = true;

        }

        private void cal_panel_button_close_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();
        }

        
        //sensitivity
        private void button_set_sensitivity_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "sensitivity";

            info_cmd_value_sensitivity.Text = get_sensor_sensitivity();

            //add sensitivity options to combo box
            set_panel_cmd_entry_combo.Items.Clear();
            set_panel_cmd_entry_combo.Items.Add("");
            set_panel_cmd_entry_combo.Items.Add("1.5 g");
            set_panel_cmd_entry_combo.Items.Add("2.0 g");
            set_panel_cmd_entry_combo.Items.Add("4.0 g");
            set_panel_cmd_entry_combo.Items.Add("6.0 g");
            set_panel_cmd_entry_combo.SelectedIndex = 0;

            //prepare the set panel
            set_panel_setup(info_cmd_label_sensitivity.Text, info_cmd_label_sensitivity.Text, "", false);

           
            info_button_sensitivity.Enabled = false;

        }

        private string get_sensor_sensitivity()
        {
            string val = "?";

            try
            {
                GET_SEN sen = new GET_SEN();
                ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(sen._Bytes);
                val = sen._Bytes[0].ToString();
            }
            catch
            {
                val = "?";
            }

            return val;
        }


        //transmission mode
        private void info_button_tr_rate_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "tr_mode";

            //add sensitivity options to combo box
            set_panel_cmd_entry_combo.Items.Clear();
            set_panel_cmd_entry_combo.Items.Add("");
            set_panel_cmd_entry_combo.Items.Add("Continuous");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 30 secs");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 60 secs");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 90 secs");
            set_panel_cmd_entry_combo.Items.Add("Burst Mode 120 secs");
            set_panel_cmd_entry_combo.SelectedIndex = 0;

            //prepare the set panel
            set_panel_setup(info_cmd_label_tr_rate.Text, info_cmd_label_tr_rate.Text, "", false);

            //read the current saved value

            //disable button
            info_button_tr_rate.Enabled = false;

        }


        //sampling rate
        private void info_button_sampling_rate_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "sampling_rate";

            //prepare the set panel
            set_panel_setup(info_cmd_label_sampling_rate.Text, info_cmd_label_sampling_rate.Text, "", true);

            //disable the sampling rate button
            info_button_sampling_rate.Enabled = false;



            //send cmd
            //GET_SR cmd = new GET_SR();
            //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(cmd._Bytes);


            //select the allowed sampling rate
            if (cur_tr_mode.CompareTo("continous") == 0)
            {
                set_panel_label_status.Text = "The Wockets is set to continous mode. \n\r This mode supports sampling rates between 1Hz and 126Hz. \n\r Enter the sampling rate in the command textbox.";
                
                //SET_SR set_sr_cmd = new SET_SR(90);
                //((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0]).Write(set_sr_cmd._Bytes);
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
            }       

        }

        //power timeout
        private void info_button_pwr_timeout_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "pwr_timeout";

            //prepare the set panel
            set_panel_setup(info_cmd_label_pwr_timeout.Text, info_cmd_label_pwr_timeout.Text, "", true);

            //read the current saved value

            //disable button
            info_button_pwr_timeout.Enabled= false;

        }


        #endregion 

        //------ Close Form ----------
        #region Close Forms
        
        private void Form7_FormClosing(object sender, FormClosingEventArgs e)
        {  close_form();
        }

        private void close_form()
        {
            if ( plotterForm != null )
            {   plotterForm.Close();
                plotterForm = null;
            }
        }

        #endregion



        private void info_button_alive_Click(object sender, EventArgs e)
        {
            set_panel_cleanup();

            current_command = "alive";

            //prepare the set panel
            set_panel_setup(info_cmd_label_alive.Text, info_cmd_label_alive.Text, "", true);

            //disable the sampling rate button
            info_button_alive.Enabled = false;

            
        }
        

       

    }//end form
}//end namespace