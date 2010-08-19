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
using Microsoft.VisualBasic;
using Microsoft.WindowsCE.Forms;

//Wockets
using Wockets;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets.Receivers;
using Wockets.Data.Types;
using Wockets.Data.Plotters;
using Wockets.Utils;
using Wockets.Utils.IPC;


//GUI
using KernelApp.GUI;


namespace KernelApp
{
    public partial class DisplayDataForm : Form
    {

        #region Varibles Declaration
       
       
        #region Wockets Parameters in data form
        
        Hashtable events = new Hashtable();
        Hashtable threads = new Hashtable();
        string kernelresponse = "";
        private TransmissionMode WocketsMode = TransmissionMode.Continuous;
       

        private Sensitivity rcv_sen = Sensitivity._4G;
        private Wockets.Data.Types.TransmissionMode rcv_tm = Wockets.Data.Types.TransmissionMode.Continuous;
        
        
        #endregion

        #region Main panels
        private int ScreenSize_Width;
        private int ScreenSize_Height;

        
#endregion 

        #region Data Panel Parameters

        #region GUI Parametes for the data panel

        private int WocketsWall_Height = 170;
        private int WocketsPlot_Height = 190;
        private int ModeButtons_Height = 63;
        private int ControlButtons_Height = 120;
        private int PhoneWall_Height = 35;
 
        //Mode Selection Buttons
       private ImageButton ContinuousButton;
        private ImageButton EfficientButton;

        //Panels within the data panel
        private PhonePanel phoneWall;
        private MainControlPanel controlsWall;

        //Plotting Panels within the data panel
        private Panel ContPlotPanel;
        private WocketsScalablePlotter ContPlotter;
        private Bitmap contBackBuffer = null;

        //Activity Count
        private PlottingPanel ActivityCountPlotter;
        private int myact = 0;

        //Timers used in the data panel
        System.Windows.Forms.Timer PlottingTimer;
        
        //Wockets Panels for the data panel
        private Dictionary<int, WocketsWall> WocketsWallList = new Dictionary<int, WocketsWall>();
       
        #endregion GUI

        #endregion Data Panel Parameters


        #endregion Varibles Declaration


        public DisplayDataForm()
        {
            InitializeComponent();

            #region Form initialization

            this.WindowState = FormWindowState.Maximized;
            ScreenSize_Width = Screen.PrimaryScreen.WorkingArea.Width;    //0x1e0 = 480
            ScreenSize_Height = Screen.PrimaryScreen.WorkingArea.Height;  //0x2ec = 748
            //ScreenSize_Width = Screen.PrimaryScreen.Bounds.Width;    //0x1e0 = 480
            //ScreenSize_Height = Screen.PrimaryScreen.Bounds.Height;  //0x2ec = 748

            //DataPanel = new Panel();
            //DataPanel.Size = new Size(ScreenSize_Width, ScreenSize_Height);
            //DataPanel.Location = new Point(0, 0);
            //DataPanel.BackColor = Color.White;

#endregion 

           
            #region Initialize Wocket
            // the wocket should be initialized before accessing the controller.
            Core.InitializeConfiguration();
            Core.InitializeController();


            //string mac = "";
            //for (int i = 0; i < CurrentWockets._Controller._Receivers.Count; i++)
            //{
            //    mac = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address;
            //    WocketsWallList[i].SetMac(mac);
            //    Core.SET_TRANSMISSION_MODE(Core._KernelGuid, mac, TransmissionMode.Continuous); 
            //}

            #endregion



            #region GUI Data Panel

            int location_y = 0;
            //Wockets Mode Buttons
            ////Efficient
            EfficientButton = new ImageButton(Resources.EfficientUnpressed2, Resources.EfficientPressed2);
            EfficientButton.Size = Resources.EfficientPressed2.Size;
            EfficientButton.Location = new Point(0, location_y);
            EfficientButton.Click += new EventHandler(changeModeEfficientClick);
            EfficientButton.Visible = true;
            EfficientButton.SetIsActive(false);
            this.Controls.Add(EfficientButton);

            ////Continuous
            ContinuousButton = new ImageButton(Resources.ContinuousUnpressed2, Resources.ContinuousPressed2);
            ContinuousButton.Size = Resources.ContinuousPressed2.Size;
            ContinuousButton.Location = new Point(240, location_y);
            ContinuousButton.Click += new EventHandler(changeModeContinuousClick);
            ContinuousButton.Visible = true;
            this.Controls.Add(ContinuousButton);
            ContinuousButton.SetIsActive(true);


            //location_y = location_y + ModeButtons_Height;
            location_y = ModeButtons_Height;

            //Phone Panel
            phoneWall = new PhonePanel(ScreenSize_Width, PhoneWall_Height, Resources.PhoneIcon2, WocketsMode);
            phoneWall.Location = new Point(0, location_y);
            this.Controls.Add(phoneWall);


           //Set Wockets Walls
            //location_y = location_y + PhoneWall_Height;
            location_y = ModeButtons_Height + PhoneWall_Height;
            
            string mac = "";
            
            if( CurrentWockets._Controller._Receivers.Count == 1)
            {
                //Wockets Wall 0
                WocketsWallList.Add(0, createWocketsWall(0, "", Resources.GreenDiamond_150));
                WocketsWallList[0].Location = new Point(0, location_y);
                this.Controls.Add(WocketsWallList[0]);

                mac = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address;
                WocketsWallList[0].SetMac(mac);
                Core.SET_TRANSMISSION_MODE(mac, TransmissionMode.Continuous);

                WocketsPlot_Height = WocketsPlot_Height + WocketsWall_Height;

               

            }
            else if (CurrentWockets._Controller._Receivers.Count == 2)
            {

                //Wockets Wall 0
                WocketsWallList.Add(0, createWocketsWall(0, "", Resources.GreenDiamond_150));
                WocketsWallList[0].Location = new Point(0, location_y);
                this.Controls.Add(WocketsWallList[0]);

                mac = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[0])._Address;
                WocketsWallList[0].SetMac(mac);
                Core.SET_TRANSMISSION_MODE( mac, TransmissionMode.Continuous);

                //update location
                location_y = ModeButtons_Height + PhoneWall_Height +WocketsWall_Height+ WocketsPlot_Height;
                //int w_location_y = location_y + WocketsWall_Height + WocketsPlot_Height;
 
                //Wockets Wall 1
                WocketsWallList.Add(1, createWocketsWall(1, "", Resources.RedSquare_150));
                WocketsWallList[1].Location = new Point(0, location_y );
                this.Controls.Add(WocketsWallList[1]);

                mac = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[1])._Address;
                WocketsWallList[1].SetMac(mac);
                Core.SET_TRANSMISSION_MODE(mac, TransmissionMode.Continuous); 

            }



            
                //update location
                //location_y = location_y + WocketsWall_Height;
                location_y = ModeButtons_Height + PhoneWall_Height +  WocketsWall_Height;

                //Continous Plotting Panel
                ContPlotPanel = new Panel();
                ContPlotPanel.BackColor = Color.White;
                ContPlotPanel.Size = new Size(ScreenSize_Width - 10, WocketsPlot_Height - 10);
                ContPlotPanel.Location = new Point(5, location_y + 5);
                ContPlotPanel.Visible = true;
                this.Controls.Add(ContPlotPanel);
                this.ContPlotPanel.Paint += new System.Windows.Forms.PaintEventHandler(this.ContPlotPanel_Paint);

                this.PlottingTimer = new System.Windows.Forms.Timer();
                this.PlottingTimer.Interval = 100;
                this.PlottingTimer.Tick += new System.EventHandler(this.PlottingTimer_Tick);

                //Initialize Plotter
                this.ContPlotter = new WocketsScalablePlotter(this.ContPlotPanel);
                this.PlottingTimer.Enabled = true;


                //Activity count panel
                ActivityCountPlotter = new PlottingPanel(ScreenSize_Width - 10, WocketsPlot_Height - 10, Color.White, Color.Green, 2);
                ActivityCountPlotter.Location = new Point(5, location_y + 5);
                ActivityCountPlotter.Visible = false;
                this.Controls.Add(ActivityCountPlotter);

                
            



            #region commented
            //this.ACountPlottingTimer = new System.Windows.Forms.Timer();
            //this.ACountPlottingTimer.Interval = 100;
            //this.ACountPlottingTimer.Tick += new System.EventHandler(this.ACountPlottingTimer_Tick);
            #endregion


            #region commented
            //location_y = location_y + WocketsPlot_Height;
            ////Wockets Wall 1
            //WocketsWallList.Add(1, createWocketsWall(1, "", Resources.RedSquare_150));
            //WocketsWallList[1].Location = new Point(0, location_y);
            //this.Controls.Add(WocketsWallList[1]);
            #endregion commented


           if (CurrentWockets._Controller._Receivers.Count == 1)
                location_y = ModeButtons_Height+ PhoneWall_Height+ WocketsPlot_Height + WocketsWall_Height;
            else
                location_y = ModeButtons_Height+ PhoneWall_Height+ WocketsPlot_Height + (2* WocketsWall_Height);


            //Main Menu Controls
            controlsWall = new MainControlPanel(ScreenSize_Width, ControlButtons_Height,
                                                Resources.left_image2, Resources.left_image_Pressed2,
                                                Resources.menu_image2, Resources.menu_image_Pressed2,
                                                Resources.right_image2, Resources.right_image_Pressed2,
                                                "Update", "Main Menu", "Next");
            controlsWall.Location = new Point(0, location_y);
            this.Controls.Add(controlsWall);

            controlsWall.MainMenuButton.Click += new EventHandler(MainMenuButtonClick);
            controlsWall.LeftButton.Click += new EventHandler(LeftButtonClick);
            controlsWall.RightButton.Click += new EventHandler(RightButtonClick);
           

            #endregion



            #region Initialize EventListener Threads

            Thread t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.BATTERY_LEVEL_UPDATED);
            t.Start();

            //t = new Thread(EventListener);
            //threads.Add(t.ManagedThreadId, t);
            //events.Add(t.ManagedThreadId, KernelResponse.BATTERY_PERCENT_UPDATED);
            //t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.PC_COUNT_UPDATED);
            t.Start();

            #region commented
            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SENSITIVITY_UPDATED);
            t.Start();

            //t = new Thread(EventListener);
            //threads.Add(t.ManagedThreadId, t);
            //events.Add(t.ManagedThreadId, KernelResponse.CALIBRATION_UPDATED);
            //t.Start();
            #endregion

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SAMPLING_RATE_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.TRANSMISSION_MODE_UPDATED);
            t.Start();


            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.ACTIVITY_COUNT_UPDATED);
            t.Start();

            #endregion


           
        }



        #region Close, Disconnect

        protected override void OnClosed(EventArgs e)
        {
            foreach (Thread t in threads.Values)
                t.Abort();
        }

        #endregion 


        #region Events Menu & Controls
        
        //Disconnect
        private void MainMenuButtonClick(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to disconnect?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                Core.Disconnect();
        }

        //Update Wockets Parameters
        private void LeftButtonClick(object sender, EventArgs e)
        {

            for (int i = 0; i < CurrentWockets._Controller._Receivers.Count; i++)
            {
                string mac = WocketsWallList[i].GetMac();

                Core.GET_WOCKET_SAMPLING_RATE(mac);
                //Core.GET_BATTERY_PERCENT(Core._KernelGuid, mac);
                Core.GET_BATTERY_LEVEL(mac);
                Core.GET_PDU_COUNT(mac);
                Core.GET_WOCKET_SENSITIVITY(mac);
            }


            //Get the phone battery 
            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
            int bt_percent = Convert.ToInt32(bpower.BatteryLifePercent);

            phoneWall.SetBTE(bt_percent, WocketsMode);
            phoneWall.UpdateBTE();


        }


        private void RightButtonClick(object sender, EventArgs e)
        {

            if( this.ContPlotPanel.Visible )
            {
                this.ContPlotPanel.Visible = false;
                this.PlottingTimer.Enabled = false;

                this.ActivityCountPlotter.Visible = true;
            }
            else
            {
                this.ContPlotPanel.Visible = true;
                this.PlottingTimer.Enabled = true;
                this.ActivityCountPlotter.Visible = true;
            }

            
        }


        private void changeModeContinuousClick(object sender, EventArgs e)
        {

            if (!ContinuousButton.GetIsActive())
            {

                try
                {


                    ContinuousButton.SetIsActive(true);
                    EfficientButton.SetIsActive(false);
                    ContinuousButton.refreshButton();
                    EfficientButton.refreshButton();

                    ContinuousButton.Enabled = false;
                    EfficientButton.Enabled = false;


                    //Set to Continuous Mode
                    WocketsMode = TransmissionMode.Continuous;


                    #region commented
                    //         //Disconnect Wockets
                    //        Core.Disconnect(Core._KernelGuid);
                    //        Thread.Sleep(1000);

                    //        //Connect Wockets
                    //        Core.Connect(Core._KernelGuid);
                    //        Thread.Sleep(1000);
                    //      
                    #endregion


                    this.ActivityCountPlotter.Visible = false;
                    this.ContPlotPanel.Visible = true;
                    this.PlottingTimer.Enabled = true;

                    for (int i = 0; i < CurrentWockets._Controller._Receivers.Count; i++)
                    {
                        Core.SET_TRANSMISSION_MODE(WocketsWallList[i].GetMac(), TransmissionMode.Continuous);
                    }




                    ContinuousButton.Enabled = true;
                    EfficientButton.Enabled = true;

                }
                catch
                {
                    //application failed to change mode, disconnect the wockets
                    //revert previous mode
                    ContinuousButton.Enabled = true;
                    EfficientButton.Enabled = true;

                }



            }


        }


        private void changeModeEfficientClick(object sender, EventArgs e)
        {

            try
            {
                if (!EfficientButton.GetIsActive())
                {
                    ContinuousButton.SetIsActive(false);
                    EfficientButton.SetIsActive(true);
                    ContinuousButton.refreshButton();
                    EfficientButton.refreshButton();

                    ContinuousButton.Enabled = false;
                    EfficientButton.Enabled = false;
                    Application.DoEvents();

                    //Efficient
                    WocketsMode = TransmissionMode.Bursty60;
                    this.ContPlotPanel.Visible = false;
                    this.PlottingTimer.Enabled = false;
                    this.ActivityCountPlotter.Visible = true;

                    for (int i = 0; i < CurrentWockets._Controller._Receivers.Count; i++)
                        Core.SET_TRANSMISSION_MODE(WocketsWallList[i].GetMac(), TransmissionMode.Bursty60);

                    ContinuousButton.Enabled = true;
                    EfficientButton.Enabled = true;

                }
            }
            catch
            {
                //application failed to change mode, disconnect the wockets
                //revert previous mode
                ContinuousButton.Enabled = true;
                EfficientButton.Enabled = true;
            
            }


        }



        

        #endregion



        #region EventListener

        private void EventListener()
        {
            int myid = System.Threading.Thread.CurrentThread.ManagedThreadId;
            KernelResponse myevent = (KernelResponse)events[myid];
            string eventName = Core.BROADCAST_EVENT_PREFIX + myevent.ToString();
            
            
            //create a new named event
            NamedEvents namedEvent = new NamedEvents();
            RegistryKey rk = null;
            //Thread.Sleep(3000);
            int ikey = 0;

            while (true)
            {
                //block for events
                namedEvent.Receive(eventName);

                switch (myevent)
                {

                    case (KernelResponse)KernelResponse.BATTERY_LEVEL_UPDATED:
                        Hashtable levels = Core.READ_BATTERY_LEVEL();
                        kernelresponse = "";
                        if (levels != null)
                        {
                            ikey = 0;
                            foreach (string s in levels.Keys)
                            {
                                WocketsWallList[ikey].SetBTP((int)levels[s]);
                                kernelresponse += s + " - " + levels[s] + "\r\n";
                                ikey++;
                            }
                        }

                        UpdateForm(myevent);
                        break;
                   

                    //case (KernelResponse)KernelResponse.BATTERY_PERCENT_UPDATED:
                    //  Hashtable percents = Core.READ_BATTERY_PERCENT();
                    //  kernelresponse = "";
                      
                      
                    //  if (percents != null)
                    //  {
                    //      ikey = 0;
                    //      foreach (string s in percents.Keys)
                    //      {
                    //          WocketsWallList[ikey].SetBTP((int)percents[s]);
                    //          kernelresponse += s + " - " + percents[s] + "\r\n";
                    //          ikey++;
                    //      }
                    //  }

                    //  UpdateForm(myevent);
                    //  break;

                    case (KernelResponse)KernelResponse.PC_COUNT_UPDATED:
                      Hashtable counts = Core.READ_PDU_COUNT();
                      kernelresponse = "";
                      if (counts != null)
                      {
                          ikey = 0;
                          foreach (string s in counts.Keys)
                          {
                              WocketsWallList[ikey].SetPC( (int)counts[s]);
                              kernelresponse += s + " - " + counts[s] + "\r\n";
                              ikey++;
                          }
                      }

                      UpdateForm(myevent);
                      break;

                   
                     case (KernelResponse)KernelResponse.SENSITIVITY_UPDATED:
                        Hashtable sensitivities = Core.READ_SENSITIVITY();
                        kernelresponse = "";
                        if (sensitivities != null)
                        {
                            ikey = 0;
                            foreach (string s in sensitivities.Keys)
                            {
                                rcv_sen = (Sensitivity)sensitivities[s];
                                WocketsWallList[ikey].SetSEN(rcv_sen);
                                kernelresponse += s + " - " + rcv_sen.ToString() + "\r\n";
                            }
                        }

                        UpdateForm(myevent);
                        break;


                     #region commented
                     //case (KernelResponse)KernelResponse.CALIBRATION_UPDATED:
                    //    Hashtable calibrations = Core.READ_CALIBRATION();
                    //    kernelresponse = "";
                    //    if (calibrations != null)
                    //    {
                    //        foreach (string s in calibrations.Keys)
                    //        {
                    //            kernelresponse += s + " - " + ((Calibration)calibrations[s])._X1G + " -" +
                    //                ((Calibration)calibrations[s])._XN1G + " -" +
                    //                ((Calibration)calibrations[s])._Y1G + " -" +
                    //                ((Calibration)calibrations[s])._YN1G + " -" +
                    //                ((Calibration)calibrations[s])._Z1G + " -" +
                    //                ((Calibration)calibrations[s])._ZN1G + " -" + "\r\n";
                    //        }
                    //    }

                    //  UpdateForm(myevent);
                    //  break;
                    #endregion commneted


                    case (KernelResponse)KernelResponse.SAMPLING_RATE_UPDATED:
                        Hashtable srs = Core.READ_SAMPLING_RATE();
                        kernelresponse = "";
                        if (srs != null)
                        {
                            ikey = 0;
                            foreach (string s in srs.Keys)
                            {
                                WocketsWallList[ikey].SetSR((int)srs[s]);
                                kernelresponse += s + " - " + WocketsWallList[ikey].GetSR().ToString() + "\r\n";
                                ikey++;
                            }
                        }

                        UpdateForm(myevent);
                        break;


                    case (KernelResponse)KernelResponse.TRANSMISSION_MODE_UPDATED:
                        Hashtable tms = Core.READ_TRANSMISSION_MODE();
                        kernelresponse = "";
                        if (tms != null)
                        {
                            ikey = 0;
                            foreach (string s in tms.Keys)
                            {
                                rcv_tm = (Wockets.Data.Types.TransmissionMode)tms[s];
                                WocketsWallList[ikey].SetMode((TransmissionMode) rcv_tm );
                                kernelresponse += s + " - " + rcv_tm.ToString() + "\r\n";
                            }
                        }

                        UpdateForm(myevent);
                        break;


                    case (KernelResponse)KernelResponse.ACTIVITY_COUNT_UPDATED:
                        Hashtable acs = Core.READ_ACTIVITY_COUNT();
                        kernelresponse = "";
                        if (acs != null)
                        {
                            ikey = 0;
                            foreach (string s in acs.Keys)
                            {
                                myact = (int)acs[s];
                                WocketsWallList[ikey].SetAC(myact);
                                kernelresponse += s + " - " + myact.ToString() + "\r\n";

                                ikey++;
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


        #region Update Functions & Callback



        delegate void UpdateFormCallback(KernelResponse response);
        public void UpdateForm(KernelResponse response)
        {
            try
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

                            #region
                            //this.menuItem15.Checked = this.menuItem16.Checked = this.menuItem17.Checked = this.menuItem18.Checked = false;
                            //switch (mysen)
                            //{
                            //    case Sensitivity._1_5G:
                            //        this.menuItem15.Checked = true;
                            //        break;
                            //    case Sensitivity._2G:
                            //        this.menuItem16.Checked = true;
                            //        break;
                            //    case Sensitivity._4G:
                            //        this.menuItem17.Checked = true;
                            //        break;
                            //    case Sensitivity._8G:
                            //        this.menuItem18.Checked = true;
                            //        break;
                            //    default:
                            //        break;

                            //}
                            #endregion

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].ClearSEN();

                            Application.DoEvents();

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].UpdateSEN();

                            break;

                        case KernelResponse.SAMPLING_RATE_UPDATED:

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].ClearSR();

                            Application.DoEvents();

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].UpdateSR();

                            break;

                        //case KernelResponse.BATTERY_PERCENT_UPDATED:

                        //    for (int i = 0; i < WocketsWallList.Count; i++)
                        //        WocketsWallList[i].ClearBTP();

                        //    Application.DoEvents();

                        //    for (int i = 0; i < WocketsWallList.Count; i++)
                        //        WocketsWallList[i].UpdateBTP();

                        //  break;
                        case KernelResponse.BATTERY_LEVEL_UPDATED:

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].ClearBTP();

                            Application.DoEvents();

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].UpdateBTP();


                            break;
                        case KernelResponse.PC_COUNT_UPDATED:

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].ClearPC();

                            Application.DoEvents();

                            for (int i = 0; i < WocketsWallList.Count; i++)
                                WocketsWallList[i].UpdatePC();

                            break;

                        #region commented
                        //            //case KernelResponse.TRANSMISSION_MODE_UPDATED:
                        //            //    this.menuItem22.Checked = this.menuItem23.Checked = this.menuItem25.Checked = this.menuItem26.Checked = this.menuItem27.Checked = false;
                        //            //    switch (mytm)
                        //            //    {
                        //            //        case Wockets.Data.Types.TransmissionMode.Continuous:
                        //            //            this.menuItem12.Checked = true;
                        //            //            break;
                        //            //        case Wockets.Data.Types.TransmissionMode.Bursty30:
                        //            //            this.menuItem23.Checked = true;
                        //            //            break;
                        //            //        case Wockets.Data.Types.TransmissionMode.Bursty60:
                        //            //            this.menuItem25.Checked = true;
                        //            //            break;
                        //            //        case Wockets.Data.Types.TransmissionMode.Bursty90:
                        //            //            this.menuItem26.Checked = true;
                        //            //            break;
                        //            //        case Wockets.Data.Types.TransmissionMode.Bursty120:
                        //            //            this.menuItem27.Checked = true;
                        //            //            break;
                        //            //        default:
                        //            //            break;

                        //            //    }
                        //            //    break;

                        #endregion

                        case KernelResponse.TRANSMISSION_MODE_UPDATED:

                            #region commented
                            //this.menuItem22.Checked = this.menuItem23.Checked = this.menuItem25.Checked = this.menuItem26.Checked = this.menuItem27.Checked = false;
                            //switch (mytm)
                            //   {
                            //       case Wockets.Data.Types.TransmissionMode.Continuous:
                            //           this.menuItem22.Checked = true;
                            //           break;
                            //       case Wockets.Data.Types.TransmissionMode.Bursty30:
                            //           this.menuItem23.Checked = true;
                            //           break;
                            //       case Wockets.Data.Types.TransmissionMode.Bursty60:
                            //           this.menuItem25.Checked = true;
                            //           break;
                            //       case Wockets.Data.Types.TransmissionMode.Bursty90:
                            //           this.menuItem26.Checked = true;
                            //           break;
                            //       case Wockets.Data.Types.TransmissionMode.Bursty120:
                            //           this.menuItem27.Checked = true;
                            //           break;
                            //       default:
                            //           break;

                            //   }
                            //   break;
                            #endregion

                            WocketsMode = rcv_tm;


                            break;

                        case KernelResponse.ACTIVITY_COUNT_UPDATED:

                            ActivityCountPlotter.updateData(myact);
                            phoneWall.UpdateStatusLabel("Act. Count: "  +  // 470"); //+ 
                            ActivityCountPlotter.shortHistoryData.Count.ToString());

                            break;

                        default:

                            break;
                    }

                }
            }
            catch( Exception e)
            { }

        }




        #endregion 

      
        #region Continuous Plotting

        private void PlottingTimer_Tick(object sender, EventArgs e)
        {
            if (ContPlotter != null)
            {
                if (contBackBuffer == null) // || (isResized))
                {
                    contBackBuffer = new Bitmap((int)(this.ContPlotPanel.Width), (int)(this.ContPlotPanel.Height));
                }

                using (Graphics g = Graphics.FromImage(contBackBuffer))
                {

                    ContPlotter.Draw(g);
                    g.Dispose();

                }
            }
        }


        void ContPlotPanel_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
        {
            if (this.ContPlotPanel.Visible)
            {
                if (contBackBuffer != null)
                    e.Graphics.DrawImage(contBackBuffer, 0, 0);
            }
        }

        #region commented
        //void ACPlotPanel_Paint(object sender, System.Windows.Forms.PaintEventArgs e)
        //{
        //    if (this.ActivityCountPlotter.Visible)
        //    {
        //        //if (contBackBuffer != null)
        //        //    e.Graphics.DrawImage(contBackBuffer, 0, 0);
        //        this.ActivityCountPlotter.updateData(myact);
        //    }
        //    else
        //    {
        //        this.ActivityCountPlotter.addData(myact);
        //    }
        //}
        #endregion 


        #endregion



        #region GUI related functions

        private WocketsWall createWocketsWall(int id, string mac, Bitmap wimage)
            {
                return new WocketsWall(id, mac, ScreenSize_Width, WocketsWall_Height, wimage, WocketsMode);
            }

        #endregion

    }
}