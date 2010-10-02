using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Utils;
using System.Threading;
using Microsoft.WindowsCE.Forms;


namespace CollectData
{
    public partial class Form1 : Form
    {
        private Thread timerThread;
        private HardwareButton hwb1;
        public Form1()
        {
            InitializeComponent();
            // Create event-handler delegate for the KeyUp
            // event for this form. This form is associated
            // with each of the hardware buttons, and the
            // event occurs when a hardware button is pressed.
            // Note that you could also use the KeyDown event
            // instead of the KeyUp event.
            this.KeyPreview = true;
            this.KeyUp += new KeyEventHandler(this.OnKeyUp);

            // Call the method to configure
            // the hardware button.
            HBConfig();

            timerThread = new Thread(new ThreadStart(TimerThread));
            timerThread.Start();
            this.label2.Text = Settings._SessionStart.ToString("dddd, MMM. d, yyyy h:mm tt");
            DiskSpace space1 = Memory.GetDiskSpace("\\");
            DiskSpace space2 = Memory.GetDiskSpace("\\Internal Storage\\");
            this.label7.Text = (space1.FreeBytesAvailable /  System.Math.Pow(2, 20)).ToString("00") + " MB";
        }


        delegate void UpdateTimeCallback();
        private bool disposed = false;

        public void UpdateTime()
        {
            if (!disposed)
            {
                if (label3.InvokeRequired)
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                {
                    UpdateTimeCallback d = new UpdateTimeCallback(UpdateTime);
                    this.Invoke(d, new object[] { });
                }
                else
                {
                    this.label3.Text = _Label3;
                }
            }
        }

        private string _Label3 = "";
        private void TimerThread()
        {
            while (true)
            {
                TimeSpan duration=DateTime.Now.Subtract(Settings._SessionStart);
                _Label3 = duration.Hours.ToString("00") + "h:" + duration.Minutes.ToString("00") + "m:" + duration.Seconds.ToString("00") + "s";
                 UpdateTime();
                Thread.Sleep(1000);
            }
        }

        // Configure hardware buttons
        // 1 and 4 to activate the current form.
        private void HBConfig()
        {
            try
            {
                hwb1 = new HardwareButton();            
                hwb1.AssociatedControl = this;                
                hwb1.HardwareKey = HardwareKeys.ApplicationKey5;                
            }
            catch (Exception exc)
            {
                MessageBox.Show(exc.Message + " Check if the hardware button is physically available on this device.");
            }
        }

        // When a hardware button is pressed and released,
        // this form receives the KeyUp event. The OnKeyUp
        // method is used to determine which hardware
        // button was pressed, because the event data
        // specifies a member of the HardwareKeys enumeration.
        private void OnKeyUp(object sender, KeyEventArgs e)
        {
            switch ((HardwareKeys)e.KeyCode)
            {
                case HardwareKeys.ApplicationKey5:
                    MessageBox.Show("TEST1");
                    break;

                case HardwareKeys.ApplicationKey4:
                    MessageBox.Show("TEST4");
                    break;

                default:
                    break;
            }
        }


        private void label23_ParentChanged(object sender, EventArgs e)
        {

        }

        private void label13_ParentChanged(object sender, EventArgs e)
        {

        }

        private void pictureBox5_Click(object sender, EventArgs e)
        {

        }

        private void pictureBox3_Click(object sender, EventArgs e)
        {

        }

        private void label22_ParentChanged(object sender, EventArgs e)
        {

        }

        private void label25_ParentChanged(object sender, EventArgs e)
        {

        }

        private void pictureBox4_Click(object sender, EventArgs e)
        {

        }

        private void label24_ParentChanged(object sender, EventArgs e)
        {

        }
    }
}