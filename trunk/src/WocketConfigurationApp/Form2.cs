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

namespace WocketConfigurationApp
{
    public partial class Form2 : Form
    {
        string macaddress = "";
        private BluetoothAddress blt_address;
        private BluetoothEndPoint blt_endPoint;
        private Guid service = new Guid("{7D124848-DFEE-47d2-AAE8-12DDC3572F84}");
        private BluetoothClient bc;

        public Form2(BluetoothAddress address)
        {
            InitializeComponent();
            this.macaddress = address.ToString();
            this.textBox2.Text = macaddress;
            this.Text = "Wocket (" + macaddress + ")";


            //Set BT Device Address
            blt_address = address;// BluetoothAddress.Parse(macaddress);
            // Create a connection channel specifying the Bluetooth-Serial end-points 
            blt_endPoint = new BluetoothEndPoint((BluetoothAddress)blt_address, service);


            bc = new BluetoothClient();
            try
            {
                BluetoothSecurity.RemoveDevice(address);
                if (BluetoothSecurity.PairRequest(address, "1234"))
                //bc.Connect(blt_endPoint);
                    bc.Client.Connect(blt_endPoint);
            }
            catch ( Exception e)
            {                
            }

        }

        private void Form2_Load(object sender, EventArgs e)
        {

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
    }
}