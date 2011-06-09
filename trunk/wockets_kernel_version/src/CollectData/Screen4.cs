using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Kernel.Types;
using Wockets.Kernel;
using System.Threading;
using Wockets;
using Wockets.Decoders.Accelerometers;
using Wockets.Sensors.Accelerometers;
using Wockets.Receivers;
using System.Threading;
using System.Runtime.InteropServices;
using Wockets.Utils;

namespace CollectData
{
    public partial class Screen4 : Panel
    {

        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
        const int SW_MINIMIZED = 6;
        Thread interfaceUpdate;
        public Screen4()
        {
            InitializeComponent();            
            //Core.SubscribeEvent(KernelResponse.ACTIVITY_COUNT_UPDATED, EventListener);
            //Core.SubscribeEvent(KernelResponse.PC_COUNT_UPDATED, EventListener);
            this.label1.Text = "Wocket "+((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address+" - "+Screens.Location1;
            this.label21.Text = "Wocket " + ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[1])._Address + " - " + Screens.Location2;
            interfaceUpdate = new Thread(new ThreadStart(UpdateInterface));
            interfaceUpdate.Start();
        }

        private void UpdateInterface()
        {
            while (true)
            {                     
                Thread.Sleep(60000);
                EventListener();
            }
        }
        delegate void UpdateFormCallback();
        /// <summary>
        /// Handles kernel response events
        /// </summary>
        /// <param name="rsp"></param>
        private void EventListener()
        {
            try
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateFormCallback d = new UpdateFormCallback(EventListener);
                    this.Invoke(d, new object[] {  });
                }
                else
                {

                    
                    Core.READ_ACTIVITY_COUNT();
                    this.label11.Text = "Val: " + ((Wocket)CurrentWockets._Controller._Sensors[0])._ActivityCount;
                    this.label12.Text = "Val: " + ((Wocket)CurrentWockets._Controller._Sensors[1])._ActivityCount;
                    Core.READ_PDU_COUNT();                    
                    this.label7.Text = "Sent: " + ((Wocket)CurrentWockets._Controller._Sensors[0])._PDUCount;
                    this.label16.Text = "Sent: " + ((Wocket)CurrentWockets._Controller._Sensors[1])._PDUCount;
                    Core.READ_RECEIVED_COUNT();
                    this.label8.Text = "Received: " + ((Wocket)CurrentWockets._Controller._Sensors[0])._ReceivedPackets;
                    this.label15.Text = "Received: " + ((Wocket)CurrentWockets._Controller._Sensors[1])._ReceivedPackets;

                    Core.READ_FULL_RECEIVED_COUNT();
                    this.label9.Text = "Full: " + ((Wocket)CurrentWockets._Controller._Sensors[0])._Full;
                    this.label14.Text = "Full: " + ((Wocket)CurrentWockets._Controller._Sensors[1])._Full;

                    Core.READ_PARTIAL_RECEIVED_COUNT();
                    this.label10.Text = "Partial: " + ((Wocket)CurrentWockets._Controller._Sensors[0])._Partial;
                    this.label13.Text = "Partial: " + ((Wocket)CurrentWockets._Controller._Sensors[1])._Partial;

                    try
                    {
                        SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                        this.label3.Text = "Phone Battery: " + bpower.BatteryLifePercent + "%";
                    }
                    catch { }
                }
            }
            catch
            {
            }
        }
        private void button1_Click(object sender, EventArgs e)
        {
            ShowWindow(Screens.screen.Handle, SW_MINIMIZED);
        }
    }
}