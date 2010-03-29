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
        ArrayList macaddresses = new ArrayList();
        BluetoothDeviceInfo[] devices = null;
        public Form1()
        {
            InitializeComponent();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
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

            if (this.listBox1.Items.Count > 0)
                this.button2.Enabled = true;
        }

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
    }
}