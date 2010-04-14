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
    public partial class Form2 : Form
    {
        BluetoothDeviceInfo wocket;
        private delegate void updateTextDelegate_Wocket();
        private delegate void updateSearchDelegate_Wocket();
        WocketsController wc;
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

 




        private void pToolStripMenuItem_Click(object sender, EventArgs e)
        {

        }

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
                        this.comboBox1.SelectedIndex = 5;
                }
                this.Refresh();
            }
        }
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
    }
}