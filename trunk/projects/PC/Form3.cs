using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Data.Plotters;
using Wockets;

namespace WocketConfigurationApp
{
    public partial class Form3 : Form
    {

        public Form3()
        {
            InitializeComponent();
            aPlotter = new WocketsScalablePlotter(this.panel1, CurrentWockets._Controller);            
        }

        private WocketsScalablePlotter aPlotter;
        private Bitmap backBuffer = null;
        private bool isResized = false;



        /// <summary>
        ///
        /// </summary>
        /// <param name="pevent"></param>
        protected override void OnPaintBackground(PaintEventArgs pevent)
        {
        }


        void Form3_Resize(object sender, System.EventArgs e)
        {
            this.timer1.Enabled = false;
            this.panel1.Width = this.Width;
            this.panel1.Height = this.Height;            
            aPlotter = new WocketsScalablePlotter(this.panel1, CurrentWockets._Controller);
            isResized = true;
            this.timer1.Enabled = true;


        }



        private void GraphAccelerometerValues()
        {
            if ((backBuffer == null) || (isResized))
            {
                backBuffer = new Bitmap((int)this.panel1.Width, (int)this.panel1.Height);
                isResized = false;
            }
            using (Graphics g = Graphics.FromImage(backBuffer))
            {

                aPlotter.Draw(g);
                g.Dispose();
            }

        }


        void panel1_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
        {
            if ((this.panel1.Visible) && (backBuffer != null))
                e.Graphics.DrawImage(backBuffer, 0, 0);
        }

        private void timer1_Tick(object sender, EventArgs e)
        {
            GraphAccelerometerValues();
        }

    }
}