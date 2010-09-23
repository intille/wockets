using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Kernel;
using System.Collections;
using Wockets.Receivers;

namespace CollectData
{
    public partial class Screen1 : Form
    {
        public Screen1()
        {
            InitializeComponent();
            this.Text = "MIT Wockets";
            System.Reflection.Assembly a = System.Reflection.Assembly.GetExecutingAssembly();
            System.Reflection.AssemblyName an = a.GetName();
            this.label2.Text = "Version " + an.Version.ToString();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            this.panel2.Visible = false;
            this.menuItem2.Enabled = this.panel1.Visible = !(this.panel1.Visible);
        }

        private void pictureBox1_Click(object sender, EventArgs e)
        {
            this.panel2.Visible = false;
            this.menuItem2.Enabled = this.panel1.Visible = !(this.panel1.Visible);
        }

        private void button2_Click(object sender, EventArgs e)
        {
            this.panel1.Visible = false;
            this.menuItem2.Enabled=this.panel2.Visible = !(this.panel2.Visible);
            
        }

        private void pictureBox2_Click(object sender, EventArgs e)
        {
            this.panel1.Visible = false;
            this.menuItem2.Enabled = this.panel2.Visible = !(this.panel2.Visible);
        }

        private void menuItem1_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                Core.Terminate();

                if (!Core._KernalStarted)
                {
                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
            }
        }


        private void menuItem2_Click(object sender, EventArgs e)
        {
            Wockets.WocketsController wc = new Wockets.WocketsController("", "", "");
            if (this.panel1.Visible)
                wc.FromXML(Core.KERNEL_PATH+"\\SensorData1.xml");
            else
                wc.FromXML(Core.KERNEL_PATH+"\\SensorData2.xml");
            ArrayList sensors = new ArrayList();
            for (int i = 0; (i < wc._Receivers.Count); i++)
                sensors.Add(((RFCOMMReceiver)wc._Receivers[i])._Address);
           
            Screens.screen2 = new Screen2(sensors);
            Screens.screen2.Show();
            this.Close();
        }
    }
}