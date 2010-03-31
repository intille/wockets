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
    public partial class Form1 : Form
    {

        BtWocketPC bt_wocket = null;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();

        private string latestReading;
        private string mac_address = ""; //"0006660250da";

        //-------------------------------------------
        //ArrayList macaddresses = new ArrayList();
        BluetoothDeviceInfo[] devices = null;
        //-------------------------------------------

        public Form1()
        {
            InitializeComponent();
        }




        private void button_search_Click(object sender, EventArgs e)
        {

            #region
            /*BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
            BluetoothClient btc = new BluetoothClient();
            
            devices = btc.DiscoverDevices(60, false, true, true);
            int wocketCount = 0;
            for (int i = 0; (i < devices.Length); i++)
            {
                //if the device is a wocket
                if (((devices[i].DeviceName.IndexOf("Wocket") >= 0) || (devices[i].DeviceName.IndexOf("WKT") >= 0) || (devices[i].DeviceName.IndexOf("FireFly") >= 0)) && (wocketCount < 100))
                {
                    string hex = "";     
                    hex = devices[i].DeviceAddress.ToString();
                    if (this.listBox1.Items.IndexOf(hex) < 0)
                    {
                        this.listBox1.Items.Add(devices[i].DeviceName + " (" + hex + ")");
                        macaddresses.Add(hex);
                    }
                    wocketCount++;
                }
            }
            btc.Dispose();
            btc.Close();
             */


            /*
            if (this.listBox1.Items.Count > 0)
                this.button2.Enabled = true;
             */
            #endregion

            
            button_search.BackColor = Color.DarkGray;
            button_search.Enabled = false;
            label_status.Text = "searching ...";

            Application.DoEvents();

            BtWocketPC bt_wocket_search = new BtWocketPC();
            System.Threading.Thread.Sleep(500);

            
            if (bt_wocket_search.Search())
            {
                devices = bt_wocket_search.GetDevicesFound();
                listBox1.DataSource = devices;
                listBox1.DisplayMember = "Device Name";
                listBox1.ValueMember = "DeviceAddress";

                button_select_wocket.Enabled = true;
                button_unselect_wocket.Enabled = false;

            }

            bt_wocket_search.Stop();


            button_search.BackColor = Color.Gainsboro;
            button_search.Enabled = true;
            label_status.Text = "Waiting for wocket...";
        }



        void OnNewReading_Wocket(object sender, EventArgs e)
        {

            latestReading = bt_wocket.LastValue.ToString();
            updateText_Wocket();

        }


        private void updateText_Wocket()
        {
            if (this.InvokeRequired)
            { this.BeginInvoke(new updateTextDelegate_Wocket(updateText_Wocket)); }
            else
            {
                //update_text_fields(2);
                textBox_info.Text = latestReading;

                //find a better way to do this
                if (bt_wocket.IsConnected())
                    label_status.Text = "Connected to " + mac_address.Substring(7) + " ...";
                else
                    label_status.Text = "Disconnected from " + mac_address.Substring(7) + " ...";
            }
        }


       
        private void button2_Click(object sender, EventArgs e)
        {
            if (this.listBox1.SelectedIndex < 0)
            {
                MessageBox.Show("Please select a wocket");
                return;
            }

            //Form2 f = new Form2(devices[this.listBox1.SelectedIndex].DeviceAddress);
            //Form2 f = new Form2(bt_wocket.GetAddress());
            //f.Show();
            //this.Visible = false;
        }

        private void Form1_FormClosing(object sender, FormClosingEventArgs e)
        {
            if( bt_wocket != null)
                bt_wocket.Stop();
        }


        int is_connected = 0;
        private void button_connect_Click(object sender, EventArgs e)
        {
            if (is_connected == 0)
            {
                bt_wocket.StartReading();
                is_connected = 1;
                button_connect.Text= "Disconnect";
                label_status.Text = "Connected to " + mac_address.Substring(7) + " ...";

                button_configure.Enabled = true;
                button_unselect_wocket.Enabled = false;

                
             
            }
            else if (is_connected == 1)
            {
                bt_wocket.Stop();
                is_connected = 0;
                button_connect.Text = "Connect";
                label_status.Text = "Disconnected from " + mac_address.Substring(7) + " ...";

                button_configure.Enabled = false;
                button_unselect_wocket.Enabled = true;
            }
        }

       

        private void button_select_wocket_Click(object sender, EventArgs e)
        {
            mac_address = listBox1.SelectedValue.ToString();

            if (mac_address.Length == 12)
            {
                bt_wocket = new BtWocketPC(mac_address, "alive");
                System.Threading.Thread.Sleep(500);
                bt_wocket.OnNewReading += new BtWocketPC.OnNewReadingEventHandler(OnNewReading_Wocket);

                label_status.Text = "Wocket " + mac_address.Substring(7) + " is waiting to connect...";

                button_connect.Enabled = true;
                button_search.Enabled = false;

                button_unselect_wocket.Enabled = true;
                button_select_wocket.Enabled = false;

            }
            else
            { label_status.Text = "The mac address is not correct."; }

        }

        private void button_unselect_wocket_Click(object sender, EventArgs e)
        {

            label_status.Text = "The device " + mac_address.Substring(7) + " was unselected.";
            textBox_info.Text = "";

            mac_address = "";
            if (bt_wocket != null)
                bt_wocket.Stop();

            button_search.Enabled = true;
            button_connect.Enabled = false;
            button_configure.Enabled = false;
            

            button_unselect_wocket.Enabled = false;
            button_select_wocket.Enabled = true;
        }







        //------------------------------------------------

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

    }
}