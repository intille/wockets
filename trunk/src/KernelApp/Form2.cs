//System 
using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Threading;
using System.Collections;

//Microsoft
using Microsoft.Win32;


//Wockets
using Wockets;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets.Receivers;
using Wockets.Data.Types;
using Wockets.Data.Plotters;
using Wockets.Utils.IPC;



namespace KernelApp
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



        #region Initialize

        public Form2()
        {
            InitializeComponent();

            //Initialize a configuration and controller structures to retrieve wockets data
            Core.InitializeConfiguration();
            Core.InitializeController();
            mac = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address;
            this.label1.Text = "Wocket " + mac+":";
            
            //Initialize Plotter
            plotter = new WocketsScalablePlotter(this.panel1);
            this.timer1.Enabled = true;

            Thread t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.BATTERY_LEVEL_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.BATTERY_PERCENT_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.PC_COUNT_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SENSITIVITY_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.CALIBRATION_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SAMPLING_RATE_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.TRANSMISSION_MODE_UPDATED);
            t.Start();

        }


        #endregion 


        #region Close

        protected override void OnClosed(EventArgs e)
        {
            foreach (Thread t in threads.Values)
                t.Abort();
        }

        #endregion 



        #region EventListener

        private void EventListener()
        {
            int myid = System.Threading.Thread.CurrentThread.ManagedThreadId;
            KernelResponse myevent = (KernelResponse)events[myid];
            string eventName = Core.BROADCAST_EVENT_PREFIX + myevent.ToString();
            NamedEvents namedEvent = new NamedEvents();
            RegistryKey rk = null;
            Thread.Sleep(3000);
            while (true)
            {
                namedEvent.Receive(eventName);

                switch (myevent)
                {
                    case (KernelResponse)KernelResponse.BATTERY_LEVEL_UPDATED:
                        Hashtable levels=Core.READ_BATTERY_LEVEL();
                        kernelresponse = "";
                        if (levels != null)
                        {
                            foreach (string s in levels.Keys)
                                kernelresponse += s + " - " + levels[s] + "\r\n";
                        }
                 
                        UpdateForm(myevent);
                        break;
                    case (KernelResponse)KernelResponse.BATTERY_PERCENT_UPDATED:
                        Hashtable percents = Core.READ_BATTERY_PERCENT();
                        kernelresponse = "";
                        if (percents != null)
                        {
                            foreach (string s in percents.Keys)
                                kernelresponse += s + " - " + percents[s] + "\r\n";
                        }

                        UpdateForm(myevent);
                        break;
                    case (KernelResponse)KernelResponse.PC_COUNT_UPDATED:
                        Hashtable counts = Core.READ_PDU_COUNT();
                        kernelresponse = "";
                        if (counts != null)
                        {
                            foreach (string s in counts.Keys)
                                kernelresponse += s + " - " + counts[s] + "\r\n";
                        }

                        UpdateForm(myevent);
                        break;
                    case (KernelResponse)KernelResponse.SENSITIVITY_UPDATED:
                        Hashtable sensitivities = Core.READ_SENSITIVITY();
                        kernelresponse = "";
                        if (sensitivities != null)
                        {
                            foreach (string s in sensitivities.Keys)
                            {
                                mysen=(Sensitivity)sensitivities[s];
                                kernelresponse += s + " - " + mysen.ToString() + "\r\n";                                
                            }
                        }

                        UpdateForm(myevent);
                        break;
                    case (KernelResponse)KernelResponse.CALIBRATION_UPDATED:
                        Hashtable calibrations = Core.READ_CALIBRATION();
                        kernelresponse = "";
                        if (calibrations != null)
                        {
                            foreach (string s in calibrations.Keys)
                            {
                                kernelresponse += s + " - " + ((Calibration)calibrations[s])._X1G +" -"  +
                                    ((Calibration)calibrations[s])._XN1G + " -" +
                                    ((Calibration)calibrations[s])._Y1G + " -" +
                                    ((Calibration)calibrations[s])._YN1G + " -" +
                                    ((Calibration)calibrations[s])._Z1G + " -" +
                                    ((Calibration)calibrations[s])._ZN1G + " -" + "\r\n";
                            }
                        }

                        UpdateForm(myevent);
                        break;

                    case (KernelResponse)KernelResponse.SAMPLING_RATE_UPDATED:
                        Hashtable srs = Core.READ_SAMPLING_RATE();
                        kernelresponse = "";
                        if (srs != null)
                        {
                            foreach (string s in srs.Keys)
                            {
                                mysr =(int) srs[s];
                                kernelresponse += s + " - " + mysr.ToString() + "\r\n";
                            }
                        }

                        UpdateForm(myevent);
                        break;

                    case (KernelResponse)KernelResponse.TRANSMISSION_MODE_UPDATED:
                        Hashtable tms = Core.READ_TRANSMISSION_MODE();
                        kernelresponse = "";
                        if (tms != null)
                        {
                            foreach (string s in tms.Keys)
                            {
                                mytm = (Wockets.Data.Types.TransmissionMode)tms[s];
                                kernelresponse += s + " - " + mytm.ToString() + "\r\n";
                            }
                        }

                        UpdateForm(myevent);
                        break;
                    default:
                        break;
                }
            }
        }

        #endregion 



        #region Delegate
        delegate void UpdateFormCallback(KernelResponse response);
        public void UpdateForm(KernelResponse response)
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
                                this.menuItem12.Checked = true;
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

        }

        #endregion




        void panel1_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
        {
            if (this.panel1.Visible)
            {
                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);
            }
        }


       





#region timer
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


#endregion



 #region MenuOptions

        //Disconnect
        private void menuItem2_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to disconnect?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                if (Core._KernelGuid != null)
                    Core.Disconnect(Core._KernelGuid);
            }
        }

        private void menuItem3_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_BATTERY_LEVEL(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_BATTERY_LEVEL";
            }
        }

        private void menuItem4_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_BATTERY_PERCENT(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_BATTERY_PERCENT";
            }
        }

        private void menuItem5_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_PDU_COUNT(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_PDU_COUNT";
            }
        }

        private void menuItem6_Click(object sender, EventArgs e)
        {
       
        }

        private void menuItem7_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_WOCKET_CALIBRATION(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_CALIBRATION";
            }
        }

        private void menuItem11_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.SET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac, 40);
                this.menuItem9.Checked = false;
                this.menuItem10.Checked = false;
                this.menuItem11.Checked = false;
                this.menuItem12.Checked = false;
                this.menuItem13.Checked = false;
                Core.GET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac);
            }
        }

        private void menuItem14_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_WOCKET_SENSITIVITY(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_SENSITIVITY";
            }
        }

        private void menuItem15_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)            
                Core.SET_WOCKET_SENSITIVITY(Core._KernelGuid, mac,Sensitivity._1_5G);            
        }

        private void menuItem16_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
                Core.SET_WOCKET_SENSITIVITY(Core._KernelGuid, mac, Sensitivity._2G);       
        }

        private void menuItem17_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
                Core.SET_WOCKET_SENSITIVITY(Core._KernelGuid, mac, Sensitivity._4G);       
        }

        private void menuItem18_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
                Core.SET_WOCKET_SENSITIVITY(Core._KernelGuid, mac, Sensitivity._8G);       
        }

        private void menuItem20_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_SAMPLING_RATE";
            }
        }

        private void menuItem9_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.SET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac, 20);
                this.menuItem9.Checked = false;
                this.menuItem10.Checked = false;
                this.menuItem11.Checked = false;
                this.menuItem12.Checked = false;
                this.menuItem13.Checked = false;
                Core.GET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac);
            }
        }

        private void menuItem10_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.SET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac, 30);
                this.menuItem9.Checked = false;
                this.menuItem10.Checked = false;
                this.menuItem11.Checked = false;
                this.menuItem12.Checked = false;
                this.menuItem13.Checked = false;
                Core.GET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac);
            }
        }

        private void menuItem12_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.SET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac, 80);
                this.menuItem9.Checked = false;
                this.menuItem10.Checked = false;
                this.menuItem11.Checked = false;
                this.menuItem12.Checked = false;
                this.menuItem13.Checked = false;
                Core.GET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac);
            }
        }

        private void menuItem13_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
                Core.SET_WOCKET_SAMPLING_RATE(Core._KernelGuid, mac, 90); 
        }

        private void menuItem24_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                Core.GET_TRANSMISSION_MODE(Core._KernelGuid, mac);
                this.label2.Text = "Sent: GET_TRANSMISSION_MODE";
            }
        }

        private void menuItem23_Click(object sender, EventArgs e)
        {

        }


        #endregion 



    }
}