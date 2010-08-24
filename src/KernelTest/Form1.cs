using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Microsoft.VisualBasic;
using System.Threading;
using System.Collections;
using Wockets.Utils.IPC;
using Microsoft.Win32;
using Wockets;
using Wockets.Receivers;

namespace KernelTest
{
    public partial class Form1 : Form
    {
        Hashtable events = new Hashtable();
        Hashtable threads = new Hashtable();
        Hashtable discovered = new Hashtable();
        public Form1()
        {
            InitializeComponent();

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
            Core.Ping();
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
                            this.status.Text = "Kernel ... started";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = true;
                            this.menuAppUnregister.Enabled = false;
                            this.menuWocket.Enabled = false;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = false;
                            this.menuItem2.Enabled = false;
                            break;
                        case KernelResponse.STARTED:
                            this.status.Text = "Kernel ... started";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = true;
                            this.menuAppUnregister.Enabled = false;
                            this.menuWocket.Enabled = false;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = false;
                            this.menuItem2.Enabled = false;
                            break;
                        case KernelResponse.STOPPED:
                            this.status.Text = "Kernel ... stopped";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = true;
                            this.menukernelstop.Enabled = false;
                            this.menuApp.Enabled = false;
                            this.menuAppRegister.Enabled = false;
                            this.menuAppUnregister.Enabled = false;
                            this.menuWocket.Enabled = false;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = false;
                            this.menuItem2.Enabled = true;
                            this.listBox1.Enabled = false;
                            break;
                        case KernelResponse.REGISTERED:
                            this.status.Text = "Kernel ... registered";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = false;
                            this.menuAppUnregister.Enabled = true;
                            this.menuWocket.Enabled = true;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = true;
                            break;
                        case KernelResponse.UNREGISTERED:
                            this.status.Text = "Kernel ... unregistered";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = true;
                            this.menuAppUnregister.Enabled = false;
                            this.menuWocket.Enabled = false;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = false;
                            break;
                        case KernelResponse.DISCOVERED:
                            this.listBox1.Items.Clear();
                            foreach (string mac in Core._DiscoveredSensors.Values)
                                this.listBox1.Items.Add(mac);
                            if (Core._DiscoveredSensors.Count > 0)
                                this.listBox1.Enabled = true;

                            this.status.Text = "Kernel ... discovered";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = false;
                            this.menuAppUnregister.Enabled = true;
                            this.menuWocket.Enabled = true;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = true;
                            break;
                        case KernelResponse.DISCONNECTED:
                            this.status.Text = "Kernel ... disconnected";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = false;
                            this.menuAppUnregister.Enabled = true;
                            this.menuWocket.Enabled = true;
                            this.menuWocketConnect.Enabled = true;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = true;
                            this.Visible = true;
                            form2.Close();
                            break;
                        case KernelResponse.CONNECTED:
                            this.status.Text = "Kernel ... connected";
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = false;
                            this.menuAppUnregister.Enabled = true;
                            this.menuWocket.Enabled = true;
                            this.menuWocketConnect.Enabled = false;
                            this.menuWocketDisconnect.Enabled = true;
                            this.menuWocketDiscover.Enabled = false;
                            form2 = new Form2();
                            form2.Text = "Wocket - " + (string)this.listBox1.Items[this.listBox1.SelectedIndex];
                            this.Visible = false;
                            form2.Show();
                            break;
                        case KernelResponse.SENSORS_UPDATED:
                            this.status.Text = "Kernel ... sensors updated " + ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address;
                            this.menukernel.Enabled = true;
                            this.menukernelstart.Enabled = false;
                            this.menukernelstop.Enabled = true;
                            this.menuApp.Enabled = true;
                            this.menuAppRegister.Enabled = false;
                            this.menuAppUnregister.Enabled = true;
                            this.menuWocket.Enabled = true;
                            this.menuWocketConnect.Enabled = true;
                            this.menuWocketDisconnect.Enabled = false;
                            this.menuWocketDiscover.Enabled = true;
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




   
        Form2 form2;



        private void menuItem2_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                if (!Core._KernalStarted)
                {
                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
            }
        }


        private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
        {
            ArrayList s = new ArrayList();
            s.Add((string)this.listBox1.Items[this.listBox1.SelectedIndex]);            
            Core.SetSensors(s);
        }


        private void menuItem8_Click(object sender, EventArgs e)
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
                if (Interaction.MsgBox("Do you want to restart it?", MsgBoxStyle.YesNo, "Kernel already running!") == MsgBoxResult.Yes)
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
            }
        }

        private void menuItem9_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                if (Core._Registered)
                    Core.Unregister();
                //Terminate the kernel
                if (Core._OutgoingChannel != null)
                    Core.Terminate();
            }
        }

        private void menuItem11_Click(object sender, EventArgs e)
        {
            Core.Register();
        }

        private void menuAppUnregister_Click(object sender, EventArgs e)
        {
            if (Core._Registered)
                Core.Unregister();
        }

        private void menuWocketDiscover_Click(object sender, EventArgs e)
        {
            this.listBox1.Enabled = false;
            this.status.Text = "Discovery started...";
            Core.Discover();
        }

        private void menuWocketConnect_Click(object sender, EventArgs e)
        {
            this.status.Text = "Connecting ... please wait";
            Core.Connect();
        }

        private void menuWocketDisconnect_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to disconnect?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                Core.Disconnect();
        }

        private void menuItem3_Click(object sender, EventArgs e)
        {
            Core.Ping();
        }
    }
}