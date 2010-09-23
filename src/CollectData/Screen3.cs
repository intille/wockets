using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Kernel;
using Wockets.Data.Plotters;
using Wockets.Kernel.Types;
using Wockets.Data.Types;

namespace CollectData
{
    public partial class Screen3 : Form
    {

        WocketsScalablePlotter plotter;
        private Bitmap backBuffer = null;

        public Screen3()
        {
            InitializeComponent();

            //Initialize Plotter
            plotter = new WocketsScalablePlotter(this.panel1);
            this.timer1.Enabled = true;
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

        private void button1_Click(object sender, EventArgs e)
        {
            if (this.button1.Text == "Wrist")
                this.button1.Text = "Ankle";
            else
                this.button1.Text = "Wrist";

        }

        private void button2_Click(object sender, EventArgs e)
        {
            if (this.button2.Text == "Wrist")
                this.button2.Text = "Ankle";
            else
                this.button1.Text = "Wrist";
        }

        void panel1_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
        {
            if (this.panel1.Visible)
            {
                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);
            }
        }

        private void timer1_Tick(object sender, EventArgs e)
        {
            if (plotter != null)
            {
                if (backBuffer == null) // || (isResized))
                {
                    backBuffer = new Bitmap(this.panel1.Width, (int)(this.panel1.Height));
                }
                using (Graphics g = Graphics.FromImage(backBuffer))
                {

                    plotter.Draw(g);
                    g.Dispose();

                }
            }
        }

        private void menuItem2_Click(object sender, EventArgs e)
        {
            Core.SET_TRANSMISSION_MODE("all", TransmissionMode.Bursty60);
            this.menuItem2.Enabled = false;
            this.timer1.Enabled = false;
            this.panel1.Visible=false;
        }
    }
}