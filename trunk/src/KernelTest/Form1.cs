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

namespace KernelTest
{
    public partial class Form1 : Form
    {
        Hashtable events = new Hashtable();
        Hashtable threads = new Hashtable();
        Hashtable discovered = new Hashtable();
        string maclabel = "";
        public Form1()
        {
            InitializeComponent();

            Thread t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.STARTED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.REGISTERED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.UNREGISTERED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.STOPPED);
            t.Start();


            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.DISCOVERED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.CONNECTED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.DISCONNECTED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SENSORS_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.CONNECTED);
            t.Start();
        }


        protected override void OnClosed(EventArgs e)
        {
            foreach (Thread t in threads.Values)
                t.Abort();
        }

        private void EventListener()
        {
            int myid = System.Threading.Thread.CurrentThread.ManagedThreadId;
            KernelResponse myevent = (KernelResponse) events[myid];
            string eventName=Core.BROADCAST_EVENT_PREFIX+myevent.ToString();
            NamedEvents namedEvent = new NamedEvents();
            RegistryKey rk = null;
            while (true)
            {
                namedEvent.Receive(eventName);
            
                switch (myevent)
                {
                    case (KernelResponse)KernelResponse.REGISTERED:
                        UpdateForm(myevent);
                        break;
                    case (KernelResponse)KernelResponse.STOPPED:
                        UpdateForm(myevent);
                        break;
                    case (KernelResponse)KernelResponse.DISCOVERED:
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
                        if (rk != null)
                        {
                            string[] sensors = rk.GetSubKeyNames();
                            rk.Close();
                            discovered.Clear();
                            if (sensors.Length > 0)
                            {
                                for (int i = 0; (i < sensors.Length); i++)
                                {

                                    rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH + "\\" + sensors[i]); ;
                                    discovered.Add((string)rk.GetValue("Name"), (string)rk.GetValue("MacAddress"));
                                    rk.Close();                           
                                }
                            }                        
                        }
                        UpdateForm(myevent);
                        break;

                    case (KernelResponse)KernelResponse.SENSORS_UPDATED:
                         rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH);
                         if (rk != null)
                         {
                             string[] sensors = rk.GetSubKeyNames();
                             rk.Close();
                             if (sensors.Length > 0)
                             {
                                 for (int i = 0; (i < sensors.Length); i++)
                                 {
                                     rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensors[i]); ;
                                     maclabel = (string)rk.GetValue("MacAddress");
                                 }
                             }
                         }
                        UpdateForm(myevent);
                        break;

                    case (KernelResponse)KernelResponse.CONNECTED:
                        Core._Connected = true;
                        UpdateForm(myevent);
                        break;

                    case (KernelResponse)KernelResponse.DISCONNECTED:
                        Core._Connected = false;
                        UpdateForm(myevent);
                        break;
                    default:
                        break;
                }
            }
        }


        delegate void UpdateFormCallback(KernelResponse response);
        Form2 form2;
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
                    case (KernelResponse)KernelResponse.REGISTERED:
                        this.status.Text = "Application...Registered";
                        this.menuItem3.Enabled = true;
                        break;
                    case (KernelResponse)KernelResponse.STOPPED:
                        this.status.Text = "Kernel... Stopped";
                        this.menuItem3.Enabled = false;
                        break;
                    case (KernelResponse)KernelResponse.DISCOVERED:
                        this.listBox1.Items.Clear();
                        foreach (string mac in discovered.Values)                        
                            this.listBox1.Items.Add(mac);
                        if (discovered.Count > 0)
                        {
                            this.listBox1.Enabled = true;
                            this.menuItem4.Enabled = true;
                        }
                        this.status.Text = "Discovery... Done";
                        break;
                    case (KernelResponse)KernelResponse.SENSORS_UPDATED:
                        this.status.Text = "Selected... "+ maclabel;            
                        break;
                    case (KernelResponse)KernelResponse.CONNECTED:
                        form2 = new Form2();
                        form2.Text = "Wocket - "+(string)this.listBox1.Items[this.listBox1.SelectedIndex];
                        this.Visible = false;
                        form2.Show();              
                        break;
                    case (KernelResponse)KernelResponse.DISCONNECTED:
                        this.Show();
                        this.Visible = true;
                        this.status.Text = "Disconnected...";
                        this.menuItem3.Enabled = true;
                        form2.Close();
                        break;
                    default:
                        break;
                }
                
            }

        }

        private void menuItem2_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                if (Core._KernelGuid != null)
                    Core.Unregister(Core._KernelGuid);
   
                //Terminate the kernel
                if (Core._KernelGuid != null)
                    Core.Send(KernelCommand.TERMINATE, Core._KernelGuid);
                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();
            }
        }

        private void menuItem3_Click(object sender, EventArgs e)
        {
            if (Core._KernelGuid != null)
            {
                this.menuItem4.Enabled = false;
                this.listBox1.Enabled = false;
                this.status.Text = "Discovery started...";
                Core.Send(KernelCommand.DISCOVER, Core._KernelGuid);
            }
        }

        private void button1_Click(object sender, EventArgs e)
        {
            button1.Enabled = false;
            if (!Core._KernelStarted)
                Core.Start();
            else
            {
                if (Interaction.MsgBox("Do you want to restart it?", MsgBoxStyle.YesNo, "Kernel already running!") == MsgBoxResult.Yes)
                {
                    //Make sure no kernels are running
                    if (Core.Terminate())
                        Core.Start();
                    else
                        MessageBox.Show("Failed to shutdown kernel");
                }

            }

            Thread.Sleep(5000);
            if (Core._KernelStarted)
            {
                if (!Core._Registered)
                {
                    Core.Register();
                    if (Core._Registered)
                    {
                        // kListenerThread = new Thread(new ThreadStart(KernelListener));
                        // kListenerThread.Start();
                    }
                }

            }
            else
                button1.Enabled = true;
             
        }

        private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
        {
            ArrayList s = new ArrayList();
            s.Add((string)this.listBox1.Items[this.listBox1.SelectedIndex]);            
            Core.SetSensors(Core._KernelGuid, s);
            this.menuItem4.Enabled = true;
        }

        private void menuItem4_Click(object sender, EventArgs e)
        {
            this.menuItem3.Enabled = false;
            this.menuItem4.Enabled = false;
            this.status.Text = "Connecting ... please wait";
            Core.Connect(Core._KernelGuid);
        }
    }
}