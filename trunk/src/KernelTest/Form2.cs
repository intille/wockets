using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Data.Plotters;
using Wockets.Kernel;
using System.Threading;
using System.Collections;
using Wockets;
using Wockets.Receivers;
using Wockets.Kernel.Types;
using Wockets.Utils.IPC;
using Microsoft.Win32;
using Wockets.Data.Types;
using Wockets.Sensors.Accelerometers;

namespace KernelTest
{
    public partial class Form2 : Form
    {
        WocketsScalablePlotter plotter;
        private Bitmap backBuffer = null;
        Hashtable events = new Hashtable();
        Hashtable threads = new Hashtable();
        string mac = "";
        string kernelresponse = "";
        Sensitivity mysen=Sensitivity._4G;
        Wockets.Data.Types.TransmissionMode mytm = Wockets.Data.Types.TransmissionMode.Continuous;
        int mysr = 90;
        int myac = 0;

        public Form2()
        {
            InitializeComponent();

            //Initialize a configuration and controller structures to retrieve wockets data
            Core.InitializeConfiguration();
     
            mac = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address;
            this.label1.Text = "Wocket " + mac + ":";

            //Initialize Plotter
            plotter = new WocketsScalablePlotter(this.panel1);
            this.timer1.Enabled = true;

            Core.SubscribeEvent(KernelResponse.BATTERY_LEVEL_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.BATTERY_PERCENT_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.PC_COUNT_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.SENSITIVITY_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.CALIBRATION_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.SAMPLING_RATE_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.TRANSMISSION_MODE_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.ACTIVITY_COUNT_UPDATED, EventListener);

        }

        protected override void OnClosing(CancelEventArgs e)
        {
            this.timer1.Enabled = false;
            plotter = null;
            Core.UnsubscribeEvent(KernelResponse.BATTERY_LEVEL_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.BATTERY_PERCENT_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.PC_COUNT_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.SENSITIVITY_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.CALIBRATION_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.SAMPLING_RATE_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.TRANSMISSION_MODE_UPDATED);
            Core.UnsubscribeEvent(KernelResponse.ACTIVITY_COUNT_UPDATED);   
        }


        private void EventListener(KernelResponse rsp)
        {
            //It is important to put this event listener in a try and catch because with an event based system, there is a chance
            //when unsubscribing to kernel events that there would be an event being handled and this can cause an object disposed
            //exception
            try
            {
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateFormCallback d = new UpdateFormCallback(EventListener);
                    this.Invoke(d, new object[] { rsp });
                }
                else
                {
                    switch (rsp)
                    {
                        case KernelResponse.BATTERY_LEVEL_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    CurrentWockets._Controller._Sensors[i]._BatteryLevel + "\r\n";
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.BATTERY_PERCENT_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    CurrentWockets._Controller._Sensors[i]._BatteryPercent + "\r\n";
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.PC_COUNT_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    CurrentWockets._Controller._Sensors[i]._PDUCount + "\r\n";
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.SENSITIVITY_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                            {
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Sensitivity.ToString() + "\r\n";

                                this.menuItem15.Checked = this.menuItem16.Checked = this.menuItem17.Checked = this.menuItem18.Checked = false;
                                switch (((Accelerometer)CurrentWockets._Controller._Sensors[i])._Sensitivity)
                                {
                                    case Sensitivity._1_5G:
                                        this.menuItem15.Checked = true;
                                        break;
                                    case Sensitivity._2G:
                                        this.menuItem16.Checked = true;
                                        break;
                                    case Sensitivity._4G:
                                        this.menuItem17.Checked = true;
                                        break;
                                    case Sensitivity._8G:
                                        this.menuItem18.Checked = true;
                                        break;
                                    default:
                                        break;

                                }
                            }
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.CALIBRATION_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                            {
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address +
                                    " - " + ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._X1G + " -" +
                                        ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._XN1G + " -" +
                                        ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._Y1G + " -" +
                                        ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._YN1G + " -" +
                                        ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._Z1G + " -" +
                                        ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._ZN1G + " -" + "\r\n";
                            }
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.SAMPLING_RATE_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    CurrentWockets._Controller._Sensors[i]._SamplingRate + "\r\n";
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.TRANSMISSION_MODE_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    ((Wocket)CurrentWockets._Controller._Sensors[i])._TransmissionMode.ToString() + "\r\n";
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        case (KernelResponse)KernelResponse.ACTIVITY_COUNT_UPDATED:
                            kernelresponse = "";
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                kernelresponse += ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address + " - " +
                                    ((Wocket)CurrentWockets._Controller._Sensors[i])._ActivityCount.ToString() + "\r\n";
                            this.label3.Text = "Received: " + kernelresponse;
                            break;
                        default:
                            break;
                    }
                }
            }catch
            {
            }
        }


        delegate void UpdateFormCallback(KernelResponse response);
      /*  public void UpdateForm(KernelResponse response)
        {
            // InvokeRequired required compares the thread ID of the
            // calling thread to the thread ID of the creating thread.
            // If these threads are different, it returns true.
            if (this.InvokeRequired || this.InvokeRequired)
            {
                UpdateFormCallback d = new UpdateFormCallback(UpdateForm);
                this.Invoke(d, new object[] { response });
            }
            else
            {
                switch (response)
                {   
                    case KernelResponse.SENSITIVITY_UPDATED:
                        this.menuItem15.Checked = this.menuItem16.Checked = this.menuItem17.Checked = this.menuItem18.Checked = false;
                        switch (mysen)
                        {
                            case Sensitivity._1_5G:
                                this.menuItem15.Checked = true;
                                break;
                            case Sensitivity._2G:
                                this.menuItem16.Checked = true;
                                break;
                            case Sensitivity._4G:
                                this.menuItem17.Checked = true;
                                break;
                            case Sensitivity._8G:
                                this.menuItem18.Checked = true;
                                break;
                            default:
                                break;

                        }
                        break;

                    case KernelResponse.SAMPLING_RATE_UPDATED:
                        this.menuItem9.Checked = this.menuItem10.Checked = this.menuItem11.Checked = this.menuItem12.Checked = this.menuItem13.Checked = false;
                        switch (mysr)
                        {
                            case 20:
                                this.menuItem9.Checked = true;
                                break;
                            case 30:
                                this.menuItem10.Checked = true;
                                break;
                            case 40:
                                this.menuItem11.Checked = true;
                                break;
                            case 80:
                                this.menuItem12.Checked = true;
                                break;
                            case 90:
                                this.menuItem13.Checked = true;
                                break;
                            default:
                                this.label3.Text = "Received: " + kernelresponse;
                                break;

                        }
                        break;
                    case KernelResponse.TRANSMISSION_MODE_UPDATED:
                        this.menuItem22.Checked = this.menuItem23.Checked = this.menuItem25.Checked = this.menuItem26.Checked = this.menuItem27.Checked = false;
                        switch (mytm)
                        {
                            case Wockets.Data.Types.TransmissionMode.Continuous:
                                this.menuItem22.Checked = true;
                                break;
                            case Wockets.Data.Types.TransmissionMode.Bursty30:
                                this.menuItem23.Checked = true;
                                break;
                            case Wockets.Data.Types.TransmissionMode.Bursty60:
                                this.menuItem25.Checked = true;
                                break;
                            case Wockets.Data.Types.TransmissionMode.Bursty90:
                                this.menuItem26.Checked = true;
                                break;
                            case Wockets.Data.Types.TransmissionMode.Bursty120:
                                this.menuItem27.Checked = true;
                                break;
                            default:
                                break;

                        }
                        break;
                    default:
                        this.label3.Text = "Received: " + kernelresponse;
                        break;
                }

            }

        }*/

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
            if (MessageBox.Show("Are you sure you want to disconnect?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                Core.Disconnect();
        }

        private void menuItem3_Click(object sender, EventArgs e)
        {
            Core.GET_BATTERY_LEVEL(mac);
            this.label2.Text = "Sent: GET_BATTERY_LEVEL";
        }

        private void menuItem4_Click(object sender, EventArgs e)
        {
            Core.GET_BATTERY_PERCENT(mac);
            this.label2.Text = "Sent: GET_BATTERY_PERCENT";
        }

        private void menuItem5_Click(object sender, EventArgs e)
        {
            Core.GET_PDU_COUNT(mac);
            this.label2.Text = "Sent: GET_PDU_COUNT";
        }

        private void menuItem6_Click(object sender, EventArgs e)
        {
       
        }

        private void menuItem7_Click(object sender, EventArgs e)
        {
            Core.GET_WOCKET_CALIBRATION(mac);
            this.label2.Text = "Sent: GET_CALIBRATION";
        }

        private void menuItem11_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SAMPLING_RATE(mac, 40);
            this.menuItem9.Checked = false;
            this.menuItem10.Checked = false;
            this.menuItem11.Checked = false;
            this.menuItem12.Checked = false;
            this.menuItem13.Checked = false;
        }

        private void menuItem14_Click(object sender, EventArgs e)
        {
            Core.GET_WOCKET_SENSITIVITY(mac);
            this.label2.Text = "Sent: GET_SENSITIVITY";
        }

        private void menuItem15_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SENSITIVITY(mac, Sensitivity._1_5G);
        }

        private void menuItem16_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SENSITIVITY(mac, Sensitivity._2G);
        }

        private void menuItem17_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SENSITIVITY(mac, Sensitivity._4G);
        }

        private void menuItem18_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SENSITIVITY(mac, Sensitivity._8G);
        }

        private void menuItem20_Click(object sender, EventArgs e)
        {
            Core.GET_WOCKET_SAMPLING_RATE(mac);
            this.label2.Text = "Sent: GET_SAMPLING_RATE";
        }

        private void menuItem9_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SAMPLING_RATE(mac, 20);
            this.menuItem9.Checked = false;
            this.menuItem10.Checked = false;
            this.menuItem11.Checked = false;
            this.menuItem12.Checked = false;
            this.menuItem13.Checked = false;
        }

        private void menuItem10_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SAMPLING_RATE(mac, 30);
            this.menuItem9.Checked = false;
            this.menuItem10.Checked = false;
            this.menuItem11.Checked = false;
            this.menuItem12.Checked = false;
            this.menuItem13.Checked = false;
        }

        private void menuItem12_Click(object sender, EventArgs e)
        {
            Core.SET_WOCKET_SAMPLING_RATE(mac, 80);
            this.menuItem9.Checked = false;
            this.menuItem10.Checked = false;
            this.menuItem11.Checked = false;
            this.menuItem12.Checked = false;
            this.menuItem13.Checked = false;
        }

        private void menuItem13_Click(object sender, EventArgs e)
        {  
            Core.SET_WOCKET_SAMPLING_RATE(mac, 90);
            this.menuItem9.Checked = false;
            this.menuItem10.Checked = false;
            this.menuItem11.Checked = false;
            this.menuItem12.Checked = false;
            this.menuItem13.Checked = false;
        }

        private void menuItem24_Click(object sender, EventArgs e)
        {
            Core.GET_TRANSMISSION_MODE(mac);
            this.label2.Text = "Sent: GET_TRANSMISSION_MODE";
        }

        private void menuItem23_Click(object sender, EventArgs e)
        {

        }

        private void menuItem25_Click(object sender, EventArgs e)
        {
            Core.SET_TRANSMISSION_MODE(mac, TransmissionMode.Bursty60);
            this.menuItem22.Checked = false;
            this.menuItem23.Checked = false;
            this.menuItem25.Checked = false;
            this.menuItem26.Checked = false;
            this.menuItem27.Checked = false;
        }

        private void menuItem28_Click(object sender, EventArgs e)
        {    
        }

        private void menuItem22_Click(object sender, EventArgs e)
        {
            this.menuItem22.Checked = false;
            this.menuItem23.Checked = false;
            this.menuItem25.Checked = false;
            this.menuItem26.Checked = false;
            this.menuItem27.Checked = false;
            Core.SET_TRANSMISSION_MODE(mac, TransmissionMode.Continuous);
        }
    }
}