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
using Wockets.Receivers;
using Wockets.Data.Commands;

namespace WocketConfigurationApp
{
    public partial class Form2 : Form
    {
        BluetoothDeviceInfo wocket;
        BtWocketPC bt_wocket = null;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        RFCOMMReceiver receiver;
        public Form2(BluetoothDeviceInfo wocket)
        {
            InitializeComponent();
            this.wocket = wocket;
            this.textBox1.Text = wocket.DeviceName;
            this.textBox2.Text = wocket.DeviceAddress.ToString();
            this.Text = "Wocket (" +wocket.DeviceAddress.ToString() + ")";
        }

        private void Form2_Load(object sender, EventArgs e)
        {
            this.label_status.Text = "Connecting...";
            
         
            this.receiver = new RFCOMMReceiver();           
            this.receiver._Address = this.wocket.DeviceAddress.ToString();
            if (this.receiver.Initialize())
            {
                this.receiver.bluetoothStream._TimeoutEnabled = false;
                this.label_status.Text = "Connected...";
            }

            for (int i=0;(i<10);i++)
                this.receiver.Write(new EnterCommandMode()._Bytes);
            //this.receiver.Write(new GET_BR()._Bytes);


  
        }

        private void label1_Click(object sender, EventArgs e)
        {
            
        }

        private void label3_Click(object sender, EventArgs e)
        {

        }

        private void label6_Click(object sender, EventArgs e)
        {

        }
        private string latestReading;

        private string mac_address = ""; //"0006660250da";
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
                // textBox_info.Text = latestReading;

                //find a better way to do this
                if (bt_wocket.IsConnected())
                    label_status.Text = "Connected to " +this.wocket.DeviceAddress.ToString().Substring(7) + " ...";
                else
                    label_status.Text = "Disconnected from " + this.wocket.DeviceAddress.ToString().Substring(7) + " ...";
            }
        }


        private void Form2_FormClosing(object sender, FormClosingEventArgs e)
        {
            if (bt_wocket != null)
                bt_wocket.Stop();
        }
    }
}