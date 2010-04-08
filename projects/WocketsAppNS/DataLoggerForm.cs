using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Windows.Forms;
using System.Runtime.InteropServices;
using System.IO;
using System.Threading;
using System.Collections;

using weka.core;
using weka.classifiers;
using weka.classifiers.trees;
using System.IO.Ports;
using System.Text.RegularExpressions;
using System.Diagnostics;
using Microsoft.Win32; 

using Wockets;
using Wockets.Utils;
using WocketsWeka;
using Wockets.Sensors;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Data.Configuration;
using Wockets.Data.Features;
using Wockets.Utils.feedback;
using Wockets.Data.Plotters;
using Wockets.Data.Annotation;
using Wockets.Data.Logger;
using WocketsAppNS.Utils;
using WocketsAppNS.Utils.Forms.Progress;
using Wockets.Utils.network;



namespace WocketsAppNS
{
    public partial class DataLoggerForm : Form, SetTextControlCallback, IDisposable
    {
       
        #region Declarations of Objects

        #region Definition of Plotting and Graphing Variables       

        #region Plotting Objects

        private bool isResized = false;
        private bool isPlotting = false;
        private Bitmap backBuffer = null;
        private WocketsScalablePlotter aWocketsPlotter;

        #endregion Plotting Objects

        #endregion Definition of Plotting and Graphing Variables

        #region Definition of different timers
        /// <summary>
        /// A Unique ID for timer of good quality data
        /// </summary>
        public const int GOOD_TIMER = 1;
        /// <summary>
        /// A unique ID for timer of all data
        /// </summary>
        public const int OVERALL_TIMER = 2;
        /// <summary>
        /// A unique ID for timer of an activity
        /// </summary>
        public const int ACTIVITY_TIMER = 3;
        /// <summary>
        /// Measures the time for good quality data during a data collection session
        /// </summary>
        private ATimer goodTimer;
        /// <summary>
        /// Measures the overall time for a data collection session
        /// </summary>
        private ATimer overallTimer;
        /// <summary>
        /// Measures the length of an activity as determined by the classifier
        /// </summary>
        private ATimer activityTimer;

        #endregion Definition of different timers

        #region GUI Delegates
        /// <summary>
        /// Delegate that sets a label from other threads
        /// </summary>
        /// <param name="label">Text for the label</param>
        /// <param name="control_id">Control ID for the label</param>
        delegate void SetTextCallback(string label, int control_id);

        #endregion GUI Delegates

        #region Definition of GUI Components
        /// <summary>
        /// A hashtable for the labels of different snesors
        /// </summary>
        private Hashtable sensorLabels;
        private Hashtable sensorStatus;
        private Hashtable sensorBattery;

        //private Panel[] panels;
        private Panel[] annotatePanelArray;
        private MenuItem[] viewsMenu = new MenuItem[6];
        private MenuItem[] annotateViewsMenu = new MenuItem[2];

        
        private Image[] batteryImg = new Image[] { (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "1.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "2.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "3.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "4.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "5.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "6.gif") };

        /// <summary>
        /// The message to be displayed by the progress thread
        /// </summary>
        private string progressMessage;
        /// <summary>
        /// The progress thread object
        /// </summary>
        private Thread aProgressThread = null;

        private Thread aPlottingThread = null;

        /// <summary>
        /// True if the progress thread should quit
        /// </summary>
        private bool progressThreadQuit = false;
        /// <summary>
        /// An array list of the different buttons of the annotator
        /// </summary>
        //private ArrayList categoryButtons;
        /// <summary>
        /// An array list that stores the current index for each button
        /// </summary>
        private ArrayList categoryDrops;
        private ArrayList buttonIndex;
        /// <summary>
        /// A variable that stores the longest label on a category button for dynamic resizing of the buttons
        /// </summary>
        private string longest_label = "";
        const int SW_MINIMIZED = 6;

        private Label[] SampLabels;

        #endregion Definition of GUI Components

        #region Sampling Rate and Activity Count Components
  
        /// <summary>
        /// Change in time since last calculation
        /// </summary>
        private long LastTime;
        private long FirstTime;
        
        #endregion Sampling Rate and Activity Count Components

        //private Sound alert = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\stop.wav");
        private Sound disconnectedAlert = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\Disconnected.wav");
        private Sound connectedAlert = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\Connected.wav");
        private Sound maxoutAlert = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\Maxout.wav");





        #region Definition of annotation objects
        /// <summary>
        /// Stores the current record that is being annotated
        /// </summary>
        //private AnnotatedRecord currentRecord;
        private Annotation currentRecord=null;

        #endregion Definition of annotation objects

        [DllImport("coredll.dll")]
        public static extern int PlaySound(
            string szSound,
            IntPtr hModule,
            int flags);

        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);

        #endregion Declarations of Objects

        public bool isPocketPC = false;

        public DataLoggerForm(string storageDirectory, Session annotatedSession)
        {
            if (WocketsAppNS.Utils.Platform.NativeMethods.GetPlatformType() == "PocketPC")
                isPocketPC = true;

            Logger.InitLogger(storageDirectory);
            RegistryKey rk = Registry.LocalMachine.OpenSubKey("System\\CurrentControlSet\\Control\\Power\\State\\Unattended", true);
            rk.SetValue("wav1:", 0, RegistryValueKind.DWord);
            rk.Close();

            this.LastTime = this.FirstTime = DateTime.Now.Ticks;
            //InitializeDataLogger(storageDirectory, annotatedSession);    

            this.storageDirectory = storageDirectory;
            this.annotatedSession = annotatedSession;
            //this.classifierConfiguration = classifierConfiguration;
            CurrentWockets._Controller._annotatedSession = this.annotatedSession;
            CurrentWockets._Controller._storageDirectory = this.storageDirectory;


            //Initialize high resolution unix timer
            WocketsTimer.InitializeTime();

            //Initialize and start GUI progress thread
            progressMessage = null;
            aProgressThread = new Thread(new ThreadStart(ProgressThread));
            aProgressThread.Start();

            //Initialize Plotting Thread
            aPlottingThread = new Thread(new ThreadStart(PlotWockets));


            #region Initialize GUI Components
            //initialize the interface components
            InitializeComponent();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing Timers ...";
            InitializeTimers();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\nInitializing GUI ...";
            InitializeInterface();
            //Initialize GUI timers
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\n";
            this.isPlotting = true;

            //SetFormPositions();            
            aWocketsPlotter = new WocketsScalablePlotter(((Panel)this.panels[VISUALIZE_PANEL]));//, CurrentWockets._Controller);

            //Override the resize event
            this.Resize += new EventHandler(OnResize);



            #endregion Initialize GUI Components

            #region Initialize Feature Extraction
            FullFeatureExtractor.Initialize(CurrentWockets._Controller, CurrentWockets._Configuration, this.annotatedSession.OverlappingActivityLists[0]);
            #endregion Initialize Feature Extraction

            #region Bluetooth reception channels initialization
            //Initialize and search for wockets connections
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing receivers ... searching " + CurrentWockets._Controller._Receivers.Count + " receivers\r\n";

            CurrentWockets._Controller.Initialize();
            receiversStatus = new ReceiverStatus[CurrentWockets._Controller._Receivers.Count];
            for (int i = 0; (i < receiversStatus.Length); i++)
                receiversStatus[i] = ReceiverStatus.Connected;


            #endregion Bluetooth reception channels initialization


            foreach (Decoder d in CurrentWockets._Controller._Decoders)
                d.Subscribe(SensorDataType.BATTERYLEVEL, new Response.ResponseHandler(this.BatteryCallback));

            //aPlottingThread.Priority = ThreadPriority.AboveNormal;
            aPlottingThread.Start();

            //Terminate the progress thread
            progressThreadQuit = true;

            //Enable all timer functions
            this.readDataTimer.Enabled = true;
        }

        private bool disposed = false;

        // Implement IDisposable.
        // Do not make this method virtual.
        // A derived class should not be able to override this method.
        public void Dispose()
        {
            Dispose(true);
            // This object will be cleaned up by the Dispose method.
            // Therefore, you should call GC.SupressFinalize to
            // take this object off the finalization queue
            // and prevent finalization code for this object
            // from executing a second time.
            GC.SuppressFinalize(this);
        }





        #region Annotator-Only Constructor
        //private WocketsController wocketsController;
        private string storageDirectory;
        private Session annotatedSession;
        //private WocketsConfiguration classifierConfiguration;


        #endregion Annotator-Only Constructor
        #region Collect Data Constructor (Wockets, MITes, Builtin)

        /// <summary>
        /// This thread creates a progress form, showing the different steps
        /// as the software loads
        /// </summary>
        private void ProgressThread()
        {
            PortableProgressForm progressForm = new PortableProgressForm();
            progressForm.Show();
            while (progressThreadQuit == false)
            {
                Thread.Sleep(5);
                if (progressMessage != null)
                {
                    progressForm.UpdateProgressBar(progressMessage);
                    progressMessage = null;
                }
                else
                    progressForm.UpdateProgressBar();
            }
            progressForm.Close();
            aProgressThread.Abort();

        }

        ReceiverStatus[] receiversStatus;        


        #endregion Collect Data Constructor (Wockets, MITes, Builtin)

       

        #region Initialization Methods

        //Initialize timers for the GUI interface
        public void InitializeTimers()
        {
            this.goodTimer = new ATimer(this, GOOD_TIMER);
            this.overallTimer = new ATimer(this, OVERALL_TIMER);
            this.activityTimer = new ATimer(this, ACTIVITY_TIMER);

        }
    
        #endregion Initialization Methods

    


        #region Resize Event Handlers

        private void OnResize(object sender, EventArgs ee)
        {

            if ((this.Width > Constants.FORM_MIN_WIDTH) && (this.Height > Constants.FORM_MIN_HEIGHT))
            {


                ((Panel)this.panels[VISUALIZE_PANEL]).Width = this.ClientSize.Width;
                ((Panel)this.panels[VISUALIZE_PANEL]).Height = this.ClientSize.Height;


                //Intialize Labels 40% of the screen

                int num_rows = (int)((CurrentWockets._Controller._Sensors.Count + 2) / 2); //additional row for HR and total sampling rate
                int textBoxHeight = ((int)(0.40 * ((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Height) - ((CurrentWockets._Controller._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
                int textBoxWidth = ((((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 2);
                int currentTextY = (int)(((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Height * 0.60);
                int leftTextX = Constants.WIDGET_SPACING + 32;
                int rightTextX = ((Constants.WIDGET_SPACING + 32) * 2) + textBoxWidth;
                int currentTextX = Constants.WIDGET_SPACING + 32;
                if (isPocketPC)
                {
                    this.button1.Width = textBoxWidth;
                    this.button1.Height = textBoxHeight;
                }
                else
                {
                    this.label1.Width = textBoxWidth;
                    this.label1.Height = textBoxHeight;
                }

                Font textFont;

                if (isPocketPC)
                {
                    textFont = this.button1.Font =
                        GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                        Constants.MAX_FONT, this.button1.Size, "textBoxAC11", this.button1.Font, (float)0.9, (float)0.9);
                }
                else
                {
                    System.Windows.Forms.Form form = new System.Windows.Forms.Form();
                    form.Size = label1.Size;
                    textFont = this.label1.Font =
                        GUIHelper.CalculateBestFitFont(form.CreateGraphics(), Constants.MIN_FONT,
                        Constants.MAX_FONT, this.label1.Size, "textBoxAC11", this.label1.Font, (float)0.9, (float)0.9);
                
                }
                
                System.Windows.Forms.Label t;

                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {

                    string labelKey = "";

                    labelKey = "W" + CurrentWockets._Controller._Sensors[i]._ID;
                    PictureBox p = (PictureBox)this.sensorStatus[labelKey];
                    p.Location = new System.Drawing.Point(currentTextX - 33, currentTextY);
                    t = (System.Windows.Forms.Label)this.sensorLabels[labelKey];
                    t.Font = textFont;
                    t.Size = new System.Drawing.Size(textBoxWidth, textBoxHeight);
                    t.Location = new System.Drawing.Point(currentTextX, currentTextY);
                    if (currentTextX == leftTextX)
                        currentTextX = rightTextX;
                    else
                    {
                        currentTextX = leftTextX;
                        currentTextY += (textBoxHeight + Constants.WIDGET_SPACING);
                    }
                }

                aWocketsPlotter = new WocketsScalablePlotter(((Panel)this.panels[VISUALIZE_PANEL]));//, CurrentWockets._Controller);

                this.isResized = true;
            }
        }

        #endregion Resize Event Handlers

        #region Click Event Handlers


        private void button_Click(object sender, EventArgs e)
        {
            Button button = (Button)sender;
            int button_id = Convert.ToInt32(button.Name);
            ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
            int nextIndex = ((int)this.buttonIndex[button_id] + 1) % category.Count;
            button.Text = category[nextIndex]._Name;
            this.buttonIndex[button_id] = nextIndex;
            if (isAnnotating)
            {
                stopAnnotation();
                startAnnotation();
            }
        }

        ArrayList selectedButtons = new ArrayList();
        char[] delimiter ={ '_' };
        Sound click = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\start.wav");
        bool isAnnotating = false;

        private void activityButton_Click(object sender, EventArgs e)
        {
            Button button = (Button)sender;
            string[] name = button.Name.Split('_');
            int category = Convert.ToInt32(name[0]);
            int index = Convert.ToInt32(name[1]);

              
            this.overallTimer.reset();
               
            System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[category];
            for (int j = 0; j < activityList.Length; j++)
            {
                if (activityList[j].BackColor == Color.DodgerBlue)
                {
                    activityList[j].BackColor = Color.SkyBlue;
                    selectedButtons.Remove(activityList[j]);
                }
                else if (index == j)
                {
                    activityList[j].BackColor = Color.DodgerBlue;
                    selectedButtons.Add(activityList[j]);
                }      
            }
                                

            if (this.currentRecord != null)
            {
                this.overallTimer.stop();
                stopAnnotation();

                TextWriter tw = new StreamWriter(this.storageDirectory + "\\AnnotationIntervals.xml");                
                tw.WriteLine(this.annotatedSession.ToXML());                
                tw.Close();
            }
            if (selectedButtons.Count > 0)
            {
                this.overallTimer.start();
                startAnnotation();
            }
        }


        ArrayList records = new ArrayList();

        private void startAnnotation()
        {
            double now = WocketsTimer.GetUnixTime();
            DateTime nowDT = new DateTime();
            WocketsTimer.GetDateTime((long)now, out nowDT);
            this.currentRecord = new Annotation();
            this.currentRecord._StartDate = nowDT.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ss'.'fffK");
            this.currentRecord._StartHour = nowDT.Hour;
            this.currentRecord._StartMinute = nowDT.Minute;
            this.currentRecord._StartSecond = nowDT.Second;
            this.currentRecord._StartMillisecond = nowDT.Millisecond;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._StartUnix = ts.TotalSeconds;

            //check all buttons values, store them and disable them
            if (((Panel)this.panels[ANNOTATE_LIST_PANEL]).Visible)
            {
                foreach (ComboBox combo in categoryDrops)
                {
                    int button_id = Convert.ToInt32(combo.Name);
                    ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                    string current_label = (string)combo.SelectedItem;
                    this.currentRecord.Activities.Add(new Activity(current_label, category._Name));
                }
            }
            else if (((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Visible)
            {
                for (int i = 0; i < selectedButtons.Count; i++)
                {
                    System.Windows.Forms.Button but = (System.Windows.Forms.Button)selectedButtons[i];
                    string[] name = but.Name.Split('_');
                    int category = Convert.ToInt32(name[0]);
                    int index = Convert.ToInt32(name[1]);
                    this.currentRecord.Activities.Add(new Activity(this.annotatedSession.OverlappingActivityLists[category][index]._Name, this.annotatedSession.OverlappingActivityLists[category]._Name));
                }
            }
            CurrentWockets._Controller.currentRecord = this.currentRecord;
        }

        private void stopAnnotation()
        {
            double now = WocketsTimer.GetUnixTime();
            DateTime nowDT = new DateTime();
            WocketsTimer.GetDateTime((long)now, out nowDT);
            this.currentRecord._EndDate = nowDT.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ss'.'fffK");
            this.currentRecord._EndHour = nowDT.Hour;
            this.currentRecord._EndMinute = nowDT.Minute;
            this.currentRecord._EndSecond = nowDT.Second;
            this.currentRecord._EndMillisecond = nowDT.Millisecond;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._EndUnix = ts.TotalSeconds;
            this.annotatedSession.Annotations.Add(this.currentRecord);
            this.currentRecord = null;
            CurrentWockets._Controller.currentRecord = null;
            
        }


        private void startStopButton_Click(object sender, EventArgs e)
        {
            lock (WocketsController.MyLock)
            {
                MenuItem item = (MenuItem)sender;
                //button state is now start
                if (item.Text.Equals("Start"))
                {


                    item.Text = "Stop";
                    this.overallTimer.reset();
                    this.overallTimer.start();
                    this.goodTimer.reset();
                    this.goodTimer.start();

                    //store the current state of the categories
                    this.currentRecord = new Annotation();
                    this.currentRecord._StartDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                    this.currentRecord._StartHour = DateTime.Now.Hour;
                    this.currentRecord._StartMinute = DateTime.Now.Minute;
                    this.currentRecord._StartSecond = DateTime.Now.Second;
                    TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                    this.currentRecord._StartUnix = ts.TotalSeconds;

                    //check all buttons values, store them and disable them
                    foreach (ComboBox combo in categoryDrops)
                    {
                        int button_id = Convert.ToInt32(combo.Name);
                        ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                        string current_label = (string)combo.SelectedItem;
                        this.currentRecord.Activities.Add(new Activity(current_label, category._Name));
                        combo.Enabled = false;
                    }
                    CurrentWockets._Controller._currentRecord = this.currentRecord;
                }

                else if (item.Text.Equals("Stop"))
                {
                    // this.stopSound.Play();
                    item.Text = "Start";
                    this.overallTimer.reset();
                    this.goodTimer.reset();

                    //store the current state of the categories
                    this.currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                    this.currentRecord._EndHour = DateTime.Now.Hour;
                    this.currentRecord._EndMinute = DateTime.Now.Minute;
                    this.currentRecord._EndSecond = DateTime.Now.Second;
                    TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                    this.currentRecord._EndUnix = ts.TotalSeconds;
                    this.annotatedSession.Annotations.Add(this.currentRecord);


                    TextWriter tw = new StreamWriter(this.storageDirectory + "\\AnnotationIntervals.xml");
                    // write a line of text to the file
                    tw.WriteLine(this.annotatedSession.ToXML());
                    // close the stream
                    tw.Close();

                    ComboBox combo = (ComboBox)this.categoryDrops[0];
                    this.categoryDrops.Clear();
                    combo.SelectedItem = combo.Items[0];
                    this.categoryDrops.Add(combo);
                    combo.Enabled = true;
                    combo.Visible = true;
                    combo.Focus();

                    this.currentRecord = null;
                    CurrentWockets._Controller._currentRecord = this.currentRecord;
                }
                CurrentWockets._Controller._annotatedSession = this.annotatedSession;
            }
        }
        private void minimize_Click(object sender, EventArgs e)
        {
            ShowWindow(this.Handle, SW_MINIMIZED);
        }

        private void plotting_Click(object sender, EventArgs e)
        {
            MenuItem mi = (MenuItem)sender;
            mi.Checked = !(mi.Checked);
            this.isPlotting = mi.Checked;
        }

        private void saving_Click(object sender, EventArgs e)
        {
            MenuItem mi = (MenuItem)sender;
            mi.Checked = !(mi.Checked);            
        }

        private void powersaver_Click(object sender, EventArgs e)
        {
            MenuItem mi = (MenuItem)sender;
            mi.Checked = !(mi.Checked);
        }






        private void view_menu_Click(object sender, EventArgs e)
        {            
            //Uncheck all checked items and make them invisible if different from sender
           
            foreach (MenuItem i in this.views.Values)
                if (i.Text != ((MenuItem)sender).Text)
                {
                    ((Panel)this.panels[i.Text]).Visible = false;
                    i.Checked = false;
                }

            //Set the visibility of the selected panel
            ((Panel)this.panels[((MenuItem)sender).Text]).Visible = ((MenuItem)sender).Checked = !((MenuItem)sender).Checked;

            //Remove panel specific menus

            if (this.mainMenu1.MenuItems.Contains(this.menuItem16))
                this.mainMenu1.MenuItems.Remove(this.menuItem16);

            //If unchecked, display the empty panel
            if (!((MenuItem)sender).Checked)
                ((Panel)this.panels[EMPTY_PANEL]).Visible = true;            
            else //otherwise activate the menus/options for the appropriate panel
            {
                ((Panel)this.panels[EMPTY_PANEL]).Visible = false;
                switch (((MenuItem)sender).Text)
                {
                    case VISUALIZE_PANEL:
                        this.isPlotting = ((MenuItem)sender).Checked;
                        //this.mainMenu1.MenuItems.Add(this.menuItem15);     
                        break;
                    case ANNOTATE_LIST_PANEL:                                
                        this.mainMenu1.MenuItems.Add(this.menuItem16);                        
                        break;
                    default:
                        break;
                }
            }

        }
      

        private void annotate_menu_Click(object sender, EventArgs e)
        {
            // Determines if click was from within Annotate menu or from outside
            if (this.mainMenu1.MenuItems.Contains(this.menuItem2))
            {
                this.mainMenu1.MenuItems.Remove(this.menuItem2);
         
            }

            if (!((MenuItem)sender).Checked)
            {
                for (int i = 0; i < annotateViewsMenu.Length; i++)
                {
                    if (this.annotateViewsMenu[i].Checked)
                    {
                        this.annotatePanelArray[i].Visible = false;
                        this.annotateViewsMenu[i].Checked = false;
                        break;
                    }
                }
                ((MenuItem)sender).Checked = true;


                for (int i = 0; i < annotateViewsMenu.Length; i++)
                {
                    if (this.annotateViewsMenu[i].Checked)
                    {
                        this.annotatePanelArray[i].Visible = true;
                        break;
                    }
                }
            }
        }


        private void quit_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                isQuitting = true;
        }

        private void menuItem11_Click(object sender, EventArgs e)
        {
            if (this.isPlotting == true)
            {
                this.isPlotting = false;
                this.menuItem11.Checked = false;
            }
            else
            {
                this.isPlotting = true;
                this.menuItem11.Checked = true;
            }
        }

        #endregion Click Event Handlers

        #region Helper Methods


        public void SetText(string label, int control_id)
        {
            // InvokeRequired required compares the thread ID of the
            // calling thread to the thread ID of the creating thread.
            // If these threads are different, it returns true.
            if (this.label1.InvokeRequired || this.label1b.InvokeRequired)
            {
                SetTextCallback d = new SetTextCallback(SetText);
                this.Invoke(d, new object[] { label, control_id });
            }
            else
            {

                if (control_id == OVERALL_TIMER)
                {
                    this.label3.Text = label;
                    this.label1.Text = CurrentWockets._Controller.extractedVectors.ToString();

                    this.label3b.Text = label;                  

                }
            }
        }




        #endregion Helper Methods


        #region Graphing functions


        /// <summary>
        ///
        /// </summary>
        /// <param name="pevent"></param>
        protected override void OnPaintBackground(PaintEventArgs pevent)
        {
        }


        private void GraphAccelerometerValues()
        {
            if ((backBuffer == null) || (isResized))
            {
                backBuffer = new Bitmap(((Panel)this.panels[VISUALIZE_PANEL]).Width, (int)(((Panel)this.panels[VISUALIZE_PANEL]).Height*0.60));
                isResized = false;                    
            }
            using (Graphics g = Graphics.FromImage(backBuffer))
            {
                                                      
                aWocketsPlotter.Draw(g);
                g.Dispose();
            }
            
        }

        private void Panel1_Paint(object sender, PaintEventArgs e)
        {

            if ((((Panel)this.panels[VISUALIZE_PANEL]).Visible) && (backBuffer != null))
                e.Graphics.DrawImage(backBuffer, 0, 0);
        }

        #endregion Graphing functions


        #region Timer Methods


        private void PlotWockets()
        {
            while (true)
            {
                if (isPlotting)
                    UpdateGraph();
            
                Thread.Sleep(50);
            }
        }


        int maxout_timer = 0;
        int disconnection_timer = 0;
        bool PlayMaxout = false;
        int totalMaxouts = 0;

        private void readDataTimer_Tick(object sender, EventArgs e)
        {
            int totalDisconnections = 0;
            bool playDisconnection = false;
        
         
             
            for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
            {
                String key = "W" + CurrentWockets._Controller._Receivers[i]._ID;

                if (receiversStatus[i] != CurrentWockets._Controller._Receivers[i]._Status)
                {
                    if (CurrentWockets._Controller._Receivers[i]._Status == ReceiverStatus.Connected)
                        connectedAlert.Play();                                         
                    else if ((CurrentWockets._Controller._Receivers[i]._Status == ReceiverStatus.Disconnected) ||
                        (CurrentWockets._Controller._Receivers[i]._Status == ReceiverStatus.Reconnecting))
                        playDisconnection = true;
                                                                   
                }
                if ((CurrentWockets._Controller._Receivers[i]._Status == ReceiverStatus.Disconnected) ||
                    (CurrentWockets._Controller._Receivers[i]._Status == ReceiverStatus.Reconnecting))
                {
                    totalDisconnections++;
                    playDisconnection = true;
                    ((PictureBox)this.sensorStatus[key]).Image = (Image)this.disconnectedWocketImage;
                }
                else //connected
                {

                    if (CurrentWockets._Controller._Decoders[i].MaxedoutSamples > 0)
                    {
                        PlayMaxout = true;
                        totalMaxouts += CurrentWockets._Controller._Decoders[i].MaxedoutSamples;
                        CurrentWockets._Controller._Decoders[i].MaxedoutSamples = 0; 
                    }

                    CurrentWockets._Controller._Receivers[i].Disconnected = 0;
                    ((PictureBox)this.sensorStatus[key]).Image = (Image)this.connectedWocketImage;
                }

                receiversStatus[i] = CurrentWockets._Controller._Receivers[i]._Status;
            }
            maxout_timer++;
            disconnection_timer++;
          
            if ((PlayMaxout) && (maxout_timer>=100))
            {
                PlayMaxout = false;
                maxout_timer = 0;
                totalMaxouts = 0;
            }
            if ((playDisconnection) && (totalDisconnections > 0) && (disconnection_timer >= 200))
            {
                for (int j = 0; (j < totalDisconnections); j++)
                {
                    disconnectedAlert.Play();
                    Thread.Sleep(200);
                }
                disconnection_timer = 0;
            }

            for (int i = 0; i < CurrentWockets._Controller._Sensors.Count; i++)
            {
                if (CurrentWockets._Controller._Sensors[i]._Class == Wockets.Sensors.SensorClasses.Wockets)
                {
                    string address = ((Wockets.Receivers.RFCOMMReceiver)((Wockets.Sensors.Accelerometers.Wocket)(CurrentWockets._Controller._Sensors[i]))._Receiver)._Address;
                    Decoder decoder = CurrentWockets._Controller._Decoders[i];
                    Receiver receiver=CurrentWockets._Controller._Receivers[i];

                    double pmaxedout5 = -1; 
                    double pmaxedout = -1;

                    if (decoder.LastSamples5Minutes>0)
                        pmaxedout5 = ((double)((double)decoder.LastMaxedout5Minutes / (double)decoder.LastSamples5Minutes))*100;
                    if (decoder.TotalSamples>0)
                        pmaxedout = ((double)((double)decoder.TotalMaxedOutSamples / (double)decoder.TotalSamples))*100;

                    double pdataloss5 = -1;
                    double pdataloss = -1;
                    double secondsSinceStart=(WocketsTimer.GetUnixTime() - CurrentWockets._Controller.StartTime)/1000;

                    if (decoder.TotalSamples > 0)
                    {
                        pdataloss = (double)decoder.TotalSamples / 90.0;
                        pdataloss /= secondsSinceStart;
                        pdataloss *= 100;
                        pdataloss = 100 - pdataloss;
                        if (pdataloss < 1.0)
                            pdataloss = 0;
                    }

                    if (decoder.LastSamples5Minutes > 0)
                    {
                        pdataloss5 = (double)decoder.LastSamples5Minutes / 90.0;
                        pdataloss5 /= ( 60);
                        pdataloss5 *= 100;
                        pdataloss5 = 100 - pdataloss5;
                        if (pdataloss5 < 1.0)
                            pdataloss5 = 0;
                    }
                    this.SampLabels[i].Text = "W" + address.Substring(address.Length - 2, 2) + ": " + (pmaxedout5 == -1 ? "?" : pmaxedout5.ToString("0.0")) + "% / " + (pmaxedout == -1 ? "?" : pmaxedout.ToString("0.0")) + "% , " + (pdataloss5 == -1 ? "?" : pdataloss5.ToString("0.0")) + "% / " + (pdataloss == -1 ? "?" : pdataloss.ToString("0.0")) + "% , " + CurrentWockets._Controller._Receivers[i].NumDisconnect + " , " + CurrentWockets._Controller._Receivers[i].TimeDisconnect + "s";
                }
            }
            
            if (isQuitting)
            {
                //this.alert.Stop();

                CurrentWockets._Controller.Dispose();

                Logger.Close();

                FullFeatureExtractor.Cleanup();
                
                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();

            }             

        }




        delegate void UpdateGraphCallback();
        public void UpdateGraph()
        {

            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (((Panel)this.panels[VISUALIZE_PANEL]).InvokeRequired)
                {
                    UpdateGraphCallback d = new UpdateGraphCallback(UpdateGraph);
                    this.Invoke(d, new object[] { });
                }
                else
                {
                    if (isPlotting)
                    {
                        GraphAccelerometerValues();
                    }
                }
            }

        }
        #endregion Timer Methods

        delegate void UpdateBatteryCallback(object sender, Wockets.Decoders.Response.ResponseArgs e);

        private void BatteryCallback(object sender, Wockets.Decoders.Response.ResponseArgs e)
        {
            if (((Panel)this.panels[VISUALIZE_PANEL]).InvokeRequired)
            {
                UpdateBatteryCallback d = new UpdateBatteryCallback(BatteryCallback);
                this.Invoke(d, new object[] {sender, e});
            }
            else
            {
                Wockets.Data.Commands.BatteryResponse br = (Wockets.Data.Commands.BatteryResponse)e._Response;
                int batteryPercent = 100;
                if (br.BatteryLevel<725)
                    batteryPercent = (int)((br.BatteryLevel / 725.0) * 100.0);
                ((Label)this.sensorLabels["W" + br.SensorID]).Text = ((Label)this.sensorLabels["W" + br.SensorID]).Text.Substring(0,3) + " " + batteryPercent + "%";
               // updateCommand("Received Battery Response: "+br.BatteryLevel);
            }
        }

    }
}