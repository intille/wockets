#region System Libraries

using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Collections;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Threading;
using System.IO;
using System.Diagnostics;
using System.Runtime.InteropServices;

#endregion



#region Microsoft Libraries

using Microsoft.VisualBasic;
using Microsoft.Win32;
using Microsoft.WindowsCE.Forms;

#endregion



#region Wockets Libraries

using Wockets;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets.Utils;
using Wockets.Utils.IPC;
using Wockets.Data.Types;
using Wockets.Data.Plotters;
using Wockets.Sensors.Accelerometers;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

#endregion






namespace KernelApp
{


#region Main Form Code


public partial class Form1 : Form
{


#region Declared Variables

           
            //Wockets Application Variables
            private Thread startupThread;
            private ArrayList sensors;
            private string sensor_set = "Set1";

            private WocketsScalablePlotter plotter;
            private Bitmap backBuffer = null;

#endregion



#region Initialize Form and Wockets Controller


public Form1()
{
      
          
    InitializeComponent();

    //Assign a name to the Main Form
    this.Text = "WocketsApp"; 
        
    
    #region Create/Update Loggers

                //Create Loggers
                Core.WRITE_LAST_UPLOAD_FAILEDFILES(0);
                Core.WRITE_LAST_UPLOAD_SUCCESSFILES(0);
                Core.WRITE_LAST_UPLOAD_NEWFILES(0);

                //Update Info
                for (int i = 0; (i < 2); i++)
                {
                    Core.WRITE_FULL_RECEIVED_COUNT(i, 0);
                    Core.WRITE_PARTIAL_RECEIVED_COUNT(i, 0);
                    Core.WRITE_EMPTY_RECEIVED_COUNT(i, 0);
                    Core.WRITE_RECEIVED_ACs(i, 0);
                    Core.WRITE_SAVED_ACs(i, 0);
                }

    #endregion


    #region Create/Initialize Controller

                //Enable Controller
                CurrentWockets._Controller = new Wockets.WocketsController("", "", "");


                //Get Sensor Information from XML file
                //Decide what pair of sensors to choose
                if (this.sensor_set.CompareTo("Set1") == 0 )
                    CurrentWockets._Controller.FromXML(Core.KERNEL_PATH + "\\SensorData1.xml");
                else
                    CurrentWockets._Controller.FromXML(Core.KERNEL_PATH + "\\SensorData2.xml");


                //Set the sensors' mac addresses in an array
                //This array can be passed as a variable across forms or panels
                sensors = new ArrayList();
                for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                    sensors.Add(((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address);

    #endregion


    #region Subscribe the kernel to events
    //This are the set of basic events to get the application connected

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
               
    #endregion


    #region Launch the thread that starts the kernel based on the wockets information found in the XML files

              startupThread = new Thread(new ThreadStart(LoadWockets));
              startupThread.Start();

    #endregion


}


#endregion



#region Thread Function: Start Kernel


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


#endregion



#region Response Callbacks


#region Message Callback

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
                this.textBox1.Text = msg;
                
        }
        catch
        { }
    }


#endregion


#region Kernel Responses Callback and EventListener(Handles Kernel Response Events)
    

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
                            UpdateMsg("Register App: Ping");
                            Core.Register();
                            break;
                        case KernelResponse.STARTED:
                            UpdateMsg("Register App: Started");
                            Core.Register();
                            break;
                        case KernelResponse.REGISTERED:
                            UpdateMsg("Verify sensors: Registered");
                            Core.SetSensors(this.sensors);
                            break;
                        case KernelResponse.SENSORS_UPDATED:
                            UpdateMsg("Connect sensors");
                            
                            //Set transmission mode
                            Core.SET_TRANSMISSION_MODE("all", TransmissionMode.Continuous);

                            Core.Connect();
                            
                            break;
                        case KernelResponse.CONNECTED:
                            //this.textBox1.Text = "Wockets connected";
                            UpdateMsg("Wockets connected");
                           
                            //Show the Macs
                            this.textBox1.Text = "Wocket " + ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address + "\r\n" +
                                                 "Wocket " + ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[1])._Address + "\r\n" +
                                                 sensor_set;                           
           
                            //Enable Plotting
                            PlotSignal();

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


#endregion


#endregion


    

#region Plot Signal
//The signal is plotter by passing a panel through the WocketsPlotter Object
//The Wockets plotter object uses back buffering to plot the data.

        //Initialize Plotter
        private void PlotSignal()
        {
            plotter = new WocketsScalablePlotter(this.panel1);
            this.timer1.Enabled = true;
        }
    

        //Use the timer to update the backbuffer
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


        //Overwrite the panel paint function
        void panel1_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
        {
            if (this.panel1.Visible)
            {
                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);
            }
        }

        
#endregion



#region Exit Application

        private void button1_Click(object sender, EventArgs e)
        {
            TerminateApp();  
        }


        public void TerminateApp()
        {
            this.timer1.Enabled = false;
            plotter = null;

            //Termite the kernel
            TerminateKernel();
        }


        private void TerminateKernel()
        {
            Core.Unregister();
            Core.Terminate();

            if (!Core._KernalStarted)
            {
                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();
            }
        }


#endregion



#region Minimize Application Button

  [DllImport("coredll.dll")]
   static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
  
  const int SW_MINIMIZED = 6;


   private void button_minimize_Click(object sender, EventArgs e)
   {
       ShowWindow(this.Handle, SW_MINIMIZED);  
   }


#endregion




 }



#endregion



}