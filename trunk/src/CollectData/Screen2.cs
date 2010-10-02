using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Kernel;
using System.Threading;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using System.Collections;

namespace CollectData
{
    public partial class Screen2 : Panel
    {

        private Thread startupThread;
        private ArrayList sensors;

        public Screen2(ArrayList sensors)
        {
            InitializeComponent();
            this.sensors = sensors;

           // Core.Terminate();
            Thread.Sleep(2000);

            // Kernel response events that the application wants to listen to
            Core.SubscribeEvent(KernelResponse.STARTED, EventListener);
            Core.SubscribeEvent(KernelResponse.REGISTERED, EventListener);
            Core.SubscribeEvent(KernelResponse.UNREGISTERED, EventListener);
            Core.SubscribeEvent(KernelResponse.STOPPED, EventListener);
            Core.SubscribeEvent(KernelResponse.DISCOVERED, EventListener);
            Core.SubscribeEvent(KernelResponse.CONNECTED, EventListener);
            Core.SubscribeEvent(KernelResponse.DISCONNECTED, EventListener);
            Core.SubscribeEvent(KernelResponse.SENSORS_UPDATED, EventListener);
            Core.SubscribeEvent(KernelResponse.PING_RESPONSE, EventListener);    
            startupThread = new Thread(new ThreadStart(LoadWockets));
            startupThread.Start();
           
        }


        delegate void UpdateMsgCallback(string msg);

        private void UpdateMsg(string msg)
        {
            try
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateMsgCallback d = new UpdateMsgCallback(UpdateMsg);
                    this.Invoke(d, new object[] { msg });
                }
                else
                    this.label2.Text = msg;

            }
            catch
            {
            }
        }

 
        delegate void UpdateFormCallback(KernelResponse response);
           /// <summary>
        /// Handles kernel response events
        /// </summary>
        /// <param name="rsp"></param>
        private void EventListener(KernelResponse rsp)
        {
            try
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateFormCallback d = new UpdateFormCallback(EventListener);
                    this.Invoke(d, new object[] { rsp });
                }
                else
                {

                    switch (rsp)
                    {
                        case KernelResponse.PING_RESPONSE:
                            UpdateMsg("Register App");
                            Core.Register();                          
                            break;
                        case KernelResponse.STARTED:
                            UpdateMsg("Register App");
                            Core.Register();                                     
                            break;
                        case KernelResponse.REGISTERED:
                            UpdateMsg("Verify sensors");
                            Core.SetSensors(this.sensors);                  
                            break;
                        case KernelResponse.SENSORS_UPDATED:
                            UpdateMsg("Connect sensors");
                            Core.Connect();                    
                            break;
                        case KernelResponse.CONNECTED:
                            this.label2.Text = "Wockets connected";
                            this.spinningProgress1.AutoIncrementFrequency = 0;
                            this.spinningProgress1.Dispose();
                            this.spinningProgress1 = null;                            
                            Screens.screen3 = new Screen3();
                            Screens.screen3.Location = new System.Drawing.Point(3, 3);
                            Screens.screen3.Name = "screen3";
                            Screens.screen3.Size = new System.Drawing.Size(474, 690);
                            Screens.screen.Controls.Add(Screens.screen3);
                            Screens.screen3.Visible = true;                           
                            this.Visible = false;
                            break;
                        default:
                            break;
                    }

                }
            }
            catch
            {
            }
        }
        private void LoadWockets()
        {      
            
           if (!Core._KernalStarted)
            {
                if (!Core.Start())
                    MessageBox.Show("Failed to start kernel");
                else
                    Thread.Sleep(5000);
            }
            else
            {
                //Make sure no kernels are running
               if (Core.Terminate())
                {
                    if (!Core.Start())
                        MessageBox.Show("Failed to start kernel");
                    else
                        Thread.Sleep(5000);
                }
                else
                    MessageBox.Show("Failed to shutdown kernel");
                
            }
           
            Thread.Sleep(5000);
            Core.Ping();
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

     
    }
}