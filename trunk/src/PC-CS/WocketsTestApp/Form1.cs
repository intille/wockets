using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Collections;
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
using System.Threading;

namespace WocketsTestApp
{
    public partial class Form1 : Form
    {

        BluetoothDeviceInfo[] devices = null;
        int wocketCount = 0;
        Hashtable bluetoothlist = new Hashtable();
        public Form1()
        {
            InitializeComponent();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            this.listBox1.Items.Clear();
            this.label2.Text = "Searching... please wait";
            this.label2.Update();
            try
            {
                BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                BluetoothClient btc = new BluetoothClient();

                devices = btc.DiscoverDevices(60, false, true, true);

                for (int i = 0; (i < devices.Length); i++)
                {
                    //if the device is a wocket
                    if (((devices[i].DeviceName.IndexOf("Wocket") >= 0)
                        || (devices[i].DeviceName.IndexOf("WKT") >= 0)
                        || (devices[i].DeviceName.IndexOf("FireFly") >= 0)
                        || (devices[i].DeviceName.IndexOf("0006660") >= 0)
                        && (wocketCount < 100)))
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


                        this.listBox1.Items.Add(hex);
                        bluetoothlist.Add(hex, devices[i]);



                        wocketCount++;
                    }
                }


                btc.Dispose();
                btc.Close();
            }
            catch
            {
                MessageBox.Show("Cannot connect: please check your Bluetooth radio is plugged in and active");
                Environment.Exit(0);
            }
        }

        private void button2_Click(object sender, EventArgs e)
        {
            if (this.listBox1.SelectedIndex >= 0)
            {
                this.label2.Text = "Testing... please wait";
                this.label2.Update();
                WocketsConfiguration configuration = new WocketsConfiguration();
                CurrentWockets._Configuration = configuration;
                WocketsController wc = new WocketsController("", "", "");
                CurrentWockets._Controller = wc;
                wc._Receivers = new ReceiverList();
                wc._Decoders = new DecoderList();
                wc._Sensors = new SensorList();
                wc._Receivers.Add(new RFCOMMReceiver());
                wc._Decoders.Add(new WocketsDecoder());
                wc._Sensors.Add(new Wocket());

                ((RFCOMMReceiver)wc._Receivers[0])._Address = ((BluetoothDeviceInfo) bluetoothlist[(string)this.listBox1.Items[this.listBox1.SelectedIndex]]).DeviceAddress.ToString();
                wc._Receivers[0]._ID = 0;
                wc._Decoders[0]._ID = 0;
                wc._Sensors[0]._Receiver = wc._Receivers[0];
                wc._Sensors[0]._Decoder = wc._Decoders[0];
                ((Accelerometer)wc._Sensors[0])._Max = 1024;
                ((Accelerometer)wc._Sensors[0])._Min = 0;
                wc._Sensors[0]._Loaded = true;

 

                //---- initialize wocket controller -------
                wc.Initialize();
                wocketCount = 0;
                while (true)
                {
                    if (wc._Receivers[0]._Status == ReceiverStatus.Connected)
                    {
                        MessageBox.Show("Success: connected to wocket.");
                        Environment.Exit(0);
                    }

                    Thread.Sleep(1000);
                    wocketCount++;
                    if (wocketCount > 20)
                    {

                        MessageBox.Show("Failed: cannot connect to wocket!");                        
                        Environment.Exit(0);
                    }
                }
            }
        }

        private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (this.listBox1.SelectedIndex>=0)
                this.button2.Enabled = true;
            else
                this.button2.Enabled = false;
        }

        private void Form1_Load(object sender, EventArgs e)
        {

        }
    }
}
