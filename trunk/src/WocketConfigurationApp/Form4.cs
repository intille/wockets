using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Text.RegularExpressions;
using System.Collections;
using System.Windows.Forms;
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;

namespace WocketConfigurationApp
{
    public partial class Form4: Form
    {


        ArrayList macaddresses = new ArrayList();
        ArrayList bluetoothlist = new ArrayList();
        BluetoothDeviceInfo[] devices = null;
        
       
        public Form4()
        {
            InitializeComponent();
        }


        //Search Button
        private void button_search_Click(object sender, EventArgs e)
        {

            this.label_status.Text = "Please wait... searching for wockets";
            this.Refresh();
            this.button_search.Enabled = false;

            //this.WocketsList_Box.Items.Clear();
            
            this.dataGridView1.Rows.Clear();
            this.macaddresses.Clear();
            int wocketCount = 0;
            
            BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
            BluetoothClient btc = new BluetoothClient();

            label_status.Text = "Searching for wockets...";
            Application.DoEvents();

            devices = btc.DiscoverDevices(60, false, true, true);

            label_status.Text = "Waiting for wocket...";
            Application.DoEvents();



            for (int i = 0; (i < devices.Length); i++)
            {
                //if the device is a wocket
                if (((devices[i].DeviceName.IndexOf("Wocket") >= 0) 
                    || (devices[i].DeviceName.IndexOf("WKT") >= 0) 
                    || (devices[i].DeviceName.IndexOf("FireFly") >= 0)) 
                    && (wocketCount < 100))
                {
                    string hex = "";
                    hex = devices[i].DeviceAddress.ToString();

                    #region Commented
                    // if (this.WocketsList_Box.Items.IndexOf(hex) < 0)
                    //{
                    //    this.WocketsList_Box.Items.Add(devices[i].DeviceName + " (" + hex + ")");
                        //macaddresses.Add(hex);
                    //}
                    #endregion Commented


                    if (this.macaddresses.IndexOf(hex) < 0)
                    {
                        int row = this.dataGridView1.Rows.Add();
                        
                        this.dataGridView1.Rows[row].Cells[0].Value = devices[i].DeviceName;
                        this.dataGridView1.Rows[row].Cells[1].Value = hex;
                        this.dataGridView1.Rows[row].Cells[2].Value = "Not tested";
                        this.dataGridView1.Rows[row].Cells[3].Value = "Not tested";
                            
                        macaddresses.Add(hex);
                        bluetoothlist.Add(devices[i]);

                    }
                    


                    wocketCount++;
                }
            }


            btc.Dispose();
            btc.Close();

            #region Commented
            // if (this.WocketsList_Box.Items.Count > 0)
            //     this.button_configure.Enabled = true;
            #endregion Commented

            if (this.dataGridView1.Rows.Count > 0)
            {
                this.button_configure.Enabled = true;
                this.button_settings.Enabled = true;
            }

            this.button_search.Enabled = true;


        }


        //Configure Button
        private void button2_Click(object sender, EventArgs e)
        {

            #region Commented
            //if (this.WocketsList_Box.SelectedIndex < 0)
           // {
           //     MessageBox.Show("Please select a wocket");
           //     return;
            // }
            #endregion commented


            if (this.dataGridView1.SelectedRows.Count <= 0)
             {
                 MessageBox.Show("Please select a wocket");
                 return;
             }

           DataGridViewRow selected_row =  this.dataGridView1.SelectedRows[0];
           int selected_device_index = selected_row.Index;

            //Form2 f = new Form2(devices[this.WocketsList_Box.SelectedIndex]);

           Form5 f = new Form5((BluetoothDeviceInfo)bluetoothlist[selected_device_index]);
           f.Show();
           //this.Visible = false;



        #region commented
           
            /*
            if (is_connected == 0)
            {
                bt_wocket.StartReading();
                is_connected = 1;
                label_status.Text = "Connected to " + mac_address.Substring(7) + " ...";

                button_configure.Enabled = true;
                button_unselect_wocket.Enabled = false;



            }
            else if (is_connected == 1)
            {
                bt_wocket.Stop();
                is_connected = 0;
                label_status.Text = "Disconnected from " + mac_address.Substring(7) + " ...";

                button_configure.Enabled = false;
                button_unselect_wocket.Enabled = true;
            }
            */

        #endregion commented

        }



        int is_connected = 0;
        public static string IsValidMAC(string macAddress)
        {
            string result = null;
            Regex rx = new Regex("^([0-9a-fA-F][0-9a-fA-F]-){5}([0-9a-fA-F][0-9a-fA-F])$", RegexOptions.IgnoreCase);
            Match m = rx.Match(macAddress);
            result = m.Groups[0].Value;


            if (result.Length == 17)
            {
                return result;
            }
            else
            {
                rx = new Regex("^([0-9a-fA-F][0-9a-fA-F]){5}([0-9a-fA-F][0-9a-fA-F])$", RegexOptions.IgnoreCase);
                Match m2 = rx.Match(macAddress);
                result = m2.Groups[0].Value;
                if (result.Length == 12)
                {
                    return result;
                }
                return null;
            }
        }



        //-----------------------------EVENTS -----------------------------------------
        #region Events

        private void button_add_wocket_Click(object sender, EventArgs e)
        {

            string macaddress = Microsoft.VisualBasic.Interaction.InputBox("Please type in the MAC address for the wocket:", "Add a New Wocket", "e.g. 00066602FEA3", 0, 0);


            if (IsValidMAC(macaddress) != null)
            {

                #region Commented
                //if (this.WocketsList_Box.Items.IndexOf(macaddress) < 0)
                //    this.WocketsList_Box.Items.Add(macaddress);
                //else
                //    MessageBox.Show("Mac address already exists in the list.");

                #endregion Commented


                if (macaddresses.IndexOf(macaddress) < 0)
                {

                    //Find device index in the list of searched devices
                    int device_index = -1;
                    int wocketCount = 0;
                    //int bt_search_pass = 0;

                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                    BluetoothClient btc = new BluetoothClient();

                    System.Threading.Thread.Sleep(1500);


                    if (devices != null)
                    {
                        if (devices.Length > 0)
                        {
                                for (int i = 0; (i < devices.Length); i++)
                                {
                                    //if the device is a wocket
                                    if (((devices[i].DeviceName.IndexOf("Wocket") >= 0)
                                        || (devices[i].DeviceName.IndexOf("WKT") >= 0)
                                        || (devices[i].DeviceName.IndexOf("FireFly") >= 0))
                                        && (wocketCount < 100))
                                    {
                                        string hex = "";
                                        hex = devices[i].DeviceAddress.ToString();


                                        if (macaddress.CompareTo(hex) == 0)
                                        {
                                            device_index = i;
                                            break;
                                        }

                                        wocketCount++;
                                    }
                                }


                                //If the mac was not found, search again for devices
                                if ( device_index <= 0)
                                {

                                    label_status.Text = "Searching for wockets...";
                                    Application.DoEvents();

                                    devices = btc.DiscoverDevices(60, false, true, true);

                                    label_status.Text = "Waiting for wocket...";
                                    Application.DoEvents();

                                }
                        }
                        else
                        {   // if search has not been performed, search for devices 
                            label_status.Text = "Searching for wockets...";
                            Application.DoEvents();

                            devices = btc.DiscoverDevices(60, false, true, true);

                            label_status.Text = "Waiting for wocket...";
                            Application.DoEvents();

                           
                        }
                    }
                    else
                    {   // if search has not been performed, search for devices 
                        label_status.Text = "Searching for wockets...";
                        Application.DoEvents();

                        devices = btc.DiscoverDevices(60, false, true, true);

                        label_status.Text = "Waiting for wocket...";
                        Application.DoEvents();

                    }

                    System.Threading.Thread.Sleep(1000);
                    btc.Close();
                    btc.Dispose();
                   

                    //Search again if device was not found
                    if( device_index <= 0 && devices != null)
                    {
                        for (int i = 0; (i < devices.Length); i++)
                        {
                            //if the device is a wocket
                            if (((devices[i].DeviceName.IndexOf("Wocket") >= 0)
                                || (devices[i].DeviceName.IndexOf("WKT") >= 0)
                                || (devices[i].DeviceName.IndexOf("FireFly") >= 0))
                                && (wocketCount < 100))
                            {
                                string hex = "";
                                hex = devices[i].DeviceAddress.ToString();


                                if (macaddress.CompareTo(hex) == 0)
                                {
                                    device_index = i;
                                    break;
                                }

                                wocketCount++;
                            }
                        }

                    
                    }




                    //If bluetooth device information found
                    if (device_index >= 0)
                    {
                        int row = this.dataGridView1.Rows.Add();

                        this.dataGridView1.Rows[row].Cells[0].Value = devices[device_index].DeviceName;
                        this.dataGridView1.Rows[row].Cells[1].Value = macaddress;
                        this.dataGridView1.Rows[row].Cells[2].Value = "Not tested";
                        this.dataGridView1.Rows[row].Cells[3].Value = "Not tested";

                        macaddresses.Add(macaddress);

                        label_status.Text = "Waiting for wocket...";
                        Application.DoEvents();
                    }



                    //update buttons
                    if (this.dataGridView1.Rows.Count > 0)
                    {
                        button_settings.Enabled = true;
                        button_configure.Enabled = true;
                    }
                    else
                    {
                        button_settings.Enabled = false;
                        button_configure.Enabled = false;
                    }


                }
                else
                    MessageBox.Show("Mac address already exists in the list.");

            }
            else
                MessageBox.Show("You entered an invalid mac address.");


            #region Commented
            /* mac_address = listBox1.SelectedValue.ToString();

            if (mac_address.Length == 12)
            {
                bt_wocket = new BtWocketPC(mac_address, "alive");
                System.Threading.Thread.Sleep(500);
                bt_wocket.OnNewReading += new BtWocketPC.OnNewReadingEventHandler(OnNewReading_Wocket);

                label_status.Text = "Wocket " + mac_address.Substring(7) + " is waiting to connect...";
                button_search.Enabled = false;

                button_unselect_wocket.Enabled = true;
                button_select_wocket.Enabled = false;

            }
            else
            { label_status.Text = "The mac address is not correct."; }*/

            #endregion commented

        }

        private void button_remove_wocket_Click(object sender, EventArgs e)
        {

            #region Commented 
            /*
            if (this.WocketsList_Box.SelectedIndex >= 0)
                this.WocketsList_Box.Items.RemoveAt(this.WocketsList_Box.SelectedIndex);
            else
            {
                MessageBox.Show("Please select a wocket");
                return;
            }
            */
            #endregion Commented


            if (this.dataGridView1.SelectedRows.Count <= 0)
            {
                MessageBox.Show("Please select a wocket");
                return;
            }

            DataGridViewRow selected_row = this.dataGridView1.SelectedRows[0];
            int selected_device_index = selected_row.Index;

            if (selected_device_index >= 0)
            {    
                 this.dataGridView1.Rows.RemoveAt(selected_device_index);
                 macaddresses.RemoveAt(selected_device_index);


                 //update buttons
                 if (this.dataGridView1.Rows.Count > 0)
                 {
                     button_settings.Enabled = true;
                     button_configure.Enabled = true;
                 }
                 else
                 {
                     button_settings.Enabled = false;
                     button_configure.Enabled = false;
                 }


            }
            else
            {
                MessageBox.Show("Please select a wocket");
                return;
            }

            #region Commented
            //if (this.WocketsList_Box.SelectedIndex >= 0)
            //    this.WocketsList_Box.Items.RemoveAt(this.WocketsList_Box.SelectedIndex);
            //else
            //{
            //    MessageBox.Show("Please select a wocket");
            //    return;
            //}
            #endregion commented

            #region Commented
            /*
            label_status.Text = "The device " + mac_address.Substring(7) + " was unselected.";
            textBox_info.Text = "";

            mac_address = "";
            if (bt_wocket != null)
                bt_wocket.Stop();

            button_search.Enabled = true;
            button_configure.Enabled = false;
            

            button_unselect_wocket.Enabled = false;
            button_select_wocket.Enabled = true;
             */
            #endregion Commented

        }

        #region Commented
        /*
        private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
        {
            button_configure.Enabled = true;
        }
         */
        #endregion Commented


       

   
        //Select a wocket by double clicking the raw
        private void dataGridView1_DoubleClick(object sender, EventArgs e)
        {
            if (this.dataGridView1.Focused)
            {
                DataGridViewRow selected_row = this.dataGridView1.SelectedRows[0];
                int selected_device_index = selected_row.Index;

                if(selected_device_index >= 0 )
                {
                    button_configure.Enabled = true;
                    button_settings.Enabled = true;
                }
            }
        }

        private void button_settings_Click(object sender, EventArgs e)
        {
            

            if (this.dataGridView1.SelectedRows.Count <= 0)
            {
                MessageBox.Show("Please select a wocket");
                return;
            }


            label_status.Text = "Loading Wocket...";
            button_settings.Enabled = false;
            Application.DoEvents();


            DataGridViewRow selected_row = this.dataGridView1.SelectedRows[0];
            int selected_device_index = selected_row.Index;
           
            Form7 f = new Form7(devices[selected_device_index]);
            f.Show();

            //this.Enabled = false;

            label_status.Text = "Wocket Loaded...";
            button_settings.Enabled = true;

        }

        private void Form4_FormClosed(object sender, FormClosedEventArgs e)
        {
            Application.Exit();
        }



        //----------------------------------------------------------------------
        #endregion Events



        #region Commented
        /*
        public static string IsValidMAC(string macAddress)
        {
            string result =null;
            Regex rx = new Regex("^([0-9a-fA-F][0-9a-fA-F]-){5}([0-9a-fA-F][0-9a-fA-F])$", RegexOptions.IgnoreCase);
            Match m = rx.Match(macAddress);
            result = m.Groups[0].Value;
            if (result.Length == 17)
            {
                return result;
            }
            else
            {
                rx = new Regex("^([0-9a-fA-F][0-9a-fA-F]){5}([0-9a-fA-F][0-9a-fA-F])$", RegexOptions.IgnoreCase);
                Match m2 = rx.Match(macAddress);
                result = m2.Groups[0].Value;
                if (result.Length == 12)
                {
                    return result;
                }
                return null;
            }
        }

        private void button3_Click(object sender, EventArgs e)
        {
           string macaddress=Microsoft.VisualBasic.Interaction.InputBox("Please type in the MAC address for the wocket:", "Add a New Wocket", "e.g. 00066602FEA3", 0, 0);
           if (IsValidMAC(macaddress)!=null)
               if (this.listBox1.Items.IndexOf(macaddress)<0)                
                   this.listBox1.Items.Add(macaddress);
               else
                   MessageBox.Show("Mac address already exists in the list.");
           else
               MessageBox.Show("You entered an invalid mac address.");
        }

        private void button4_Click(object sender, EventArgs e)
        {
            if (this.listBox1.SelectedIndex >= 0)
                this.listBox1.Items.RemoveAt(this.listBox1.SelectedIndex);
            else
            {
                MessageBox.Show("Please select a wocket");
                return;
            }
        }

        private void button2_Click(object sender, EventArgs e)
        {
            if (this.listBox1.SelectedIndex < 0)
            {
                MessageBox.Show("Please select a wocket");
                return;
            }

            Form2 f = new Form2(devices[this.listBox1.SelectedIndex].DeviceAddress);
            f.Show();
            this.Visible = false;
        }
          
         */

        #endregion Commented

    }
}