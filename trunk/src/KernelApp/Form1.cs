//System Libraries
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

//Microsoft Libraries
using Microsoft.VisualBasic;
using Microsoft.Win32;
using Microsoft.WindowsCE.Forms;

//Wockets Libraries
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets.Utils.IPC;
using KernelApp.GUI;


namespace KernelApp
{   


    public partial class Form1 : Form
    {
        Hashtable events = new Hashtable();
        Hashtable threads = new Hashtable();
        int screen_width = Screen.PrimaryScreen.WorkingArea.Width;
        int screen_height = Screen.PrimaryScreen.WorkingArea.Height;
        
        
        
        
        
        Hashtable discovered = new Hashtable();
        string maclabel = "";


        SlidingList wocketsList = null;
        ArrayList selectedWockets = new ArrayList();
          
        int discoveryPanel_width = Screen.PrimaryScreen.WorkingArea.Width - 12;
        int discoveryPanel_height = 450;
        int discoveryWocketPanel_width = Screen.PrimaryScreen.WorkingArea.Width- 12;
        int discoveryWocketPanel_height = 60;



        public Form1()
        {
            InitializeComponent();

            this.WindowState = FormWindowState.Maximized;

#region GUI

            wocketsList = new SlidingList(discoveryPanel_width, discoveryPanel_height);
            wocketsList.Visible = true;
            wocketsList.Enabled = false;
            wocketsList.Location = new Point(6,40);
            this.Controls.Add(wocketsList);

            //Hard Coded Sensors, added to the display list
            int wocket_index = 0;
            WocketListItem wi = new WocketListItem("000666043e57", wocket_index, discoveryWocketPanel_width, discoveryWocketPanel_height);
            wi.Location = new Point(0, wi.Height * wocket_index);
            wi.Click += new EventHandler(wocketClickHandler);
            wocketsList.Controls.Add(wi);

           
      
#endregion


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
        //Form2 form2;
        DisplayDataForm display_data_form = null;

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
                        this.status.Text = "Started... Please select your wockets.";
                        this.menuItem3.Enabled = true; 
                        this.wocketsList.Enabled = true;
                        
                        if( selectedWockets.Count > 0)
                           this.menuItem4.Enabled = true;
                           
                       break;

                    case (KernelResponse)KernelResponse.STOPPED:
                        this.status.Text = "Kernel... Stopped";
                        this.menuItem3.Enabled = false;
                        break;
                    case (KernelResponse)KernelResponse.DISCOVERED:
                       
                        
                        //this.listBox1.Items.Clear();
                        //foreach (string mac in discovered.Values)                        
                        //    this.listBox1.Items.Add(mac);
                        
                        wocketsList.Controls.Clear();
                        int i = 0;
                        foreach (string mac in discovered.Values)
                        {
                           
                            WocketListItem wi = new WocketListItem(mac, i, discoveryWocketPanel_width, discoveryWocketPanel_height);
                            wi.Location = new Point(0, wi.Height * i);
                            wi.Click += new EventHandler(wocketClickHandler);
                            //wi.checkButton.Click += new EventHandler(wocketClickHandler);
                            wocketsList.Controls.Add(wi);
                            i++;
                        }

                        if (discovered.Count > 0)
                        {
                            //this.listBox1.Enabled = true;
                            this.wocketsList.Enabled = true;
                            this.menuItem4.Enabled = true;
                        }
                        this.status.Text = "Discovery... Done";
                        break;
                    case (KernelResponse)KernelResponse.SENSORS_UPDATED:
                        this.status.Text = "Sensors updated...";            
                        break;
                    case (KernelResponse)KernelResponse.CONNECTED:
                        //form2 = new Form2();
                        //form2.Text = "Wocket - " + (string)this.listBox1.Items[this.listBox1.SelectedIndex];
                        //this.Visible = false;
                        //form2.Show();    

                        //if (display_data_form == null)
                        //{
                            display_data_form = new DisplayDataForm();
                            display_data_form.Text = "Wocket - mac";
                            //display_data_form.Text = "Wocket - " + (string)this.listBox1.Items[this.listBox1.SelectedIndex];
                            
                            this.Visible = false;
                            display_data_form.Show();
                        //}
                        //else 
                        //{  
                        //    //if(!display_data_form.IsChangingMode()) 
                        //    //write in the display form that the wocket has been connected
                        //    //write a callback or keep a variable that is updated in this page 

                            
                        //}

                        break;
                    case (KernelResponse)KernelResponse.DISCONNECTED:

                        if (display_data_form != null)
                        {
                            //if (!display_data_form.IsChangingMode())    
                            //{
                                this.Show();
                                this.Visible = true;
                                this.status.Text = "Disconnected...";
                                this.menuItem3.Enabled = true;

                                //form2.Close();

                                display_data_form.Close();
                                this.WindowState = FormWindowState.Maximized;

                            //}
                            //else
                            //{   //write in the display form that the wocket has been disconnected
                            //    //write a callback or keep a variable that is updated in this page 
                            //}
                        }
                        

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
                    
                Core.Unregister();   
                //Terminate the kernel
                Core.Terminate();

                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();
            }
        }

      

        private void button1_Click(object sender, EventArgs e)
        {
            button1.Enabled = false;

            if (!Core._KernelStarted)
                Core.Start();
            else
            {
                if (Interaction.MsgBox("Do you want to start it?", MsgBoxStyle.YesNo, "") == MsgBoxResult.Yes)
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

        //private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
        //{
        //    ArrayList s = new ArrayList();
        //    //s.Add((string)this.listBox1.Items[this.listBox1.SelectedIndex]);
        //    if( selectedWockets.Count >0)
        //    {
        //        //restricted to 2 for the demo
        //        for (int i = 0; i < selectedWockets.Count; i++)
        //        {
        //            WocketListItem wi = (WocketListItem)selectedWockets[i];
        //            s.Add(wi._MacAddress);
        //        }
        //    }


        //    Core.SetSensors(Core._KernelGuid, s);
        //    this.menuItem4.Enabled = true;
        //}


        //Discover
        private void menuItem3_Click(object sender, EventArgs e)
        {

            this.menuItem4.Enabled = false;
            //this.listBox1.Enabled = false;
            this.wocketsList.Enabled = false;

            this.status.Text = "Discovery started...";
            Core.Discover();

        }


        private void SetSelectedSensors()
        {
            ArrayList s = new ArrayList();
            
            if ( selectedWockets.Count> 0)
            {
                for (int i = 0; i < selectedWockets.Count; i++)
                {
                    WocketListItem wi = (WocketListItem) selectedWockets[i];
                    s.Add(wi._MacAddress);
                }
            }

            Core.SetSensors(s);
        }


        //Connect
        private void menuItem4_Click(object sender, EventArgs e)
        {

            SetSelectedSensors();
            Thread.Sleep(1000);

            //this.menuItem3.Enabled = false;
           // this.menuItem4.Enabled = false;
            this.status.Text = "Connecting ... please wait";
            Core.Connect();

           
        }


        private void wocketClickHandler(object sender, EventArgs e)
        {
            WocketListItem wi = (WocketListItem)sender;
            //int name = Convert.ToInt32(wi.Mac);
            //wi.SetSelected(true);

            //if ((wi.AddCheckButton(wi.LastX, wi.LastY)) && !selectedWockets.Contains(wi))
            //if (wi.checkButton.Checked && !selectedWockets.Contains(wi))
            //if (wi.GetSelected() && !selectedWockets.Contains(wi))
            if (!selectedWockets.Contains(wi))
            {
                //wi.BackColor = Color.Yellow;
                //wi.Refresh();
                //Thread.Sleep(50);

                selectedWockets.Add(wi);
                
                
                //wi.BackColor = wi.selected_color;
                //wi.Refresh();
                wi.SetSelection(true);

            }
            //else if ( (!wi.checkButton.Checked) && selectedWockets.Contains(wi))
            //else if (!wi.GetSelected() && selectedWockets.Contains(wi))
            else if (selectedWockets.Contains(wi))
            {
                //wi.BackColor = Color.Yellow;
                //wi.Refresh();
                //Thread.Sleep(50);


                selectedWockets.Remove(wi);
                //wi.checkButton.Checked = false;
                //wi.BackColor = Color.FromArgb(245, 219, 186);
                
                //wi.BackColor = wi.bg_color;
                //wi.Refresh();
                wi.SetSelection(false);
            }

            //The wockets must be sorted in order to be consistent
            selectedWockets.Sort();

            //enable to connect if we have availabel wockets
            if (selectedWockets.Count >= 1)
            {   
                this.menuItem4.Enabled= true; 
            }
            else
            { this.menuItem4.Enabled = false; }

            
            
#region commented
            /* else                        
             {
                 bluetoothName.Text = wi._Name;                
                 this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Visible = true;
                 this.panels[ControlID.WOCKETS_PANEL].Visible = false;
                 currentPanel = ControlID.WOCKETS_CONFIGURATION_PANEL;
             }*/
#endregion


        }


    }
}