using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Threading;
using Wockets.Kernel;
using Wockets;

namespace CollectData
{
    public partial class Screen6 : Panel
    {
        public string _Address="";
        public string _Full="";
        public string _Lost="";
        public string _Partial = "";
        public int _ID = 0;
        Thread poller;
        System.Windows.Forms.Timer ScreenUpdater;

        public Screen6()
        {
            InitializeComponent();
            ScreenUpdater = new System.Windows.Forms.Timer();
            ScreenUpdater.Interval = 500;
            ScreenUpdater.Tick += new EventHandler(ScreenUpdater_Tick);
        }

        void ScreenUpdater_Tick(object sender, EventArgs e)
        {
            Core.READ_EMPTY_RECEIVED_COUNT();
            Core.READ_FULL_RECEIVED_COUNT();
            Core.READ_PARTIAL_RECEIVED_COUNT();
            Core.READ_RECEIVED_ACs();
            Core.READ_SAVED_ACs();


            this.label18.Text = CurrentWockets._Controller._Sensors[_ID]._Address;
            this.label4.Text = CurrentWockets._Controller._Sensors[_ID]._Full + " batches";
            this.label7.Text = CurrentWockets._Controller._Sensors[_ID]._Partial + " batches";
            this.label10.Text = CurrentWockets._Controller._Sensors[_ID]._Empty + " batches";
            this.label3.Text = "Sensor " + _ID;
            //this.label13.Text = CurrentWockets._Controller._Sensors[_ID]._ReceivedACs + " counts";
            this.label21.Text = "new:" + CurrentWockets._Controller._Sensors[_ID]._SavedACs + " - total:" + CurrentWockets._Controller._Sensors[_ID]._TotalSavedACs;
            this.label22.Text = "last:" + CurrentWockets._Controller._Sensors[_ID]._ReceivedACs + " - total:" + CurrentWockets._Controller._Sensors[_ID]._TotalReceivedACs;                        
        }


        delegate void UpdateScreen6Callback();

        
         /// <summary>
        /// Handles kernel response events
        /// </summary>
        /// <param name="rsp"></param>
        private void EventListener()
        {
            try
            {                
                Core.READ_EMPTY_RECEIVED_COUNT();
                Core.READ_FULL_RECEIVED_COUNT();
                Core.READ_PARTIAL_RECEIVED_COUNT();
                Core.READ_RECEIVED_ACs();
                Core.READ_SAVED_ACs();
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateScreen6Callback d = new UpdateScreen6Callback(EventListener);
                    this.Invoke(d, new object[] { });
                }
                else
                {


                    this.label18.Text = CurrentWockets._Controller._Sensors[_ID]._Address;
                    this.label4.Text = CurrentWockets._Controller._Sensors[_ID]._Full + " batches";
                    this.label7.Text = CurrentWockets._Controller._Sensors[_ID]._Partial + " batches";
                    this.label10.Text = CurrentWockets._Controller._Sensors[_ID]._Empty + " batches";
                    this.label3.Text = "Sensor " + _ID;
                    //this.label13.Text = CurrentWockets._Controller._Sensors[_ID]._ReceivedACs + " counts";
                    this.label21.Text = "new:"+CurrentWockets._Controller._Sensors[_ID]._SavedACs + " - total:" + CurrentWockets._Controller._Sensors[_ID]._TotalSavedACs;
                    this.label21.Invalidate();
                    this.label22.Text = "last:"+CurrentWockets._Controller._Sensors[_ID]._ReceivedACs + " - total:" + CurrentWockets._Controller._Sensors[_ID]._TotalReceivedACs;
                    this.label22.Invalidate();

                    this.Invalidate();

                }
            }
            catch (Exception e)
            {
            }
        }

        public void Start()
        {

            //poller = new Thread(new ThreadStart(Update));
            //poller.Start();
            ScreenUpdater.Enabled = true;
        }

        public void Stop()
        {
            //poller = new Thread(new ThreadStart(Update));
            //poller.Start();
            ScreenUpdater.Enabled = false;
        }

        private void Update()
        {

            while (true)
            {
                EventListener();
                Thread.Sleep(5000);
            }
        
        }


        private void button1_Click(object sender, EventArgs e)
        {
            //this.button1.Text = (this.button1.Text == "Ankle" ? "Wrist" : "Ankle");
        }
    }
}