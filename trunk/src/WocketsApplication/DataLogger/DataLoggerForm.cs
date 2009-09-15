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


using Wockets;
using Wockets.Utils;
using WocketsWeka;
using Wockets.Sensors;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Data.Classifiers;
using Wockets.Data.Classifiers.Utils;
using Wockets.Data.Classifiers.Trees;
using Wockets.Data.Plotters;
using Wockets.Data.Annotation;
using Wockets.Data.Logger;
using WocketsApplication.Utils;
using WocketsApplication.Utils.Forms.Progress;
using Wockets.Utils.network;
using WocketsApplication.Feedback;



namespace WocketsApplication.DataLogger
{
    public partial class DataLoggerForm : Form, SetTextControlCallback
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

        private Label[] ActGUIlabels;
        private Label[] SampLabels;

        #endregion Definition of GUI Components

        #region Sampling Rate and Activity Count Components
        /// <summary>
        /// Last time of rate calculation
        /// </summary>
        private int SRcounter=0;
        /// <summary>
        /// Change in time since last calculation
        /// </summary>
        private long LastTime;
        private long FirstTime;
        
        #endregion Sampling Rate and Activity Count Components

        private Sound alert = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\stop.wav");
        private bool play_sound = false;



        #region Definition of classification variables

        /// <summary>
        /// The classifier object that is used to do activity recognition
        /// </summary>
        private Classifier classifier;
        /// <summary>
        /// The feature vector that lists all features used by the classifier
        /// </summary>
        private FastVector fvWekaAttributes;
        /// <summary>
        /// A list of instances that are used for training or intializing a classifier
        /// </summary>
        private Instances instances;
        /// <summary>
        /// Stores the formatted labels for the classifier
        /// </summary>
        private string[] activityLabels;
        /// <summary>
        /// Stores the index of each label for fast search
        /// </summary>
        private Hashtable labelIndex;
        /// <summary>
        /// Stores counters for each label to be used during smoothening
        /// </summary>
        private int[] labelCounters;

        #endregion Definition of classification variables

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

        public DataLoggerForm(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration, int mode)
        {
            if (WocketsApplication.Utils.Platform.NativeMethods.GetPlatformType() == "PocketPC")
                isPocketPC = true;

            Logger.InitLogger(storageDirectory);
            this.LastTime = this.FirstTime = DateTime.Now.Ticks;
            if (mode == 1)
                InitializeAnnotator(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 2)
                InitializeDataLogger(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 3)
                InitializeActivityTracker(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 4)
                InitializeExergame(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
           

        }

        #region Annotator-Only Constructor
        private WocketsController wocketsController;
        private string storageDirectory;
        private Session annotatedSession;
        private DTConfiguration classifierConfiguration;

        public void InitializeAnnotator(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration)
        {
            this.storageDirectory = storageDirectory;
            this.wocketsController = wocketsController;
            this.annotatedSession = annotatedSession;
            this.classifierConfiguration = classifierConfiguration;

            //Initialize the UNIX QueryPerformanceCounter
            WocketsTimer.InitializeTime();  
            //initialize the interface components
            InitializeComponent();
            InitializeTimers();
            //Initialize different GUI components
            InitializeInterface();


        }

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

        public void InitializeDataLogger(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration)
        {
            this.storageDirectory = storageDirectory;
            this.wocketsController = wocketsController;
            this.annotatedSession = annotatedSession;
            this.classifierConfiguration = classifierConfiguration;

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
            aWocketsPlotter = new WocketsScalablePlotter(((Panel)this.panels[VISUALIZE_PANEL]), this.wocketsController);

            //Override the resize event
            this.Resize += new EventHandler(OnResize);



            #endregion Initialize GUI Components

            #region Initialize Feature Extraction
            FeatureExtractor.Initialize(this.wocketsController, this.classifierConfiguration, this.annotatedSession.OverlappingActivityLists[0]);
            #endregion Initialize Feature Extraction

            #region Bluetooth reception channels initialization
            //Initialize and search for wockets connections
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing receivers ... searching " + this.wocketsController._Receivers.Count + " receivers\r\n";            

            this.wocketsController.Initialize();

            #endregion Bluetooth reception channels initialization

            aPlottingThread.Start();

            //Terminate the progress thread
            progressThreadQuit = true;

            //Enable all timer functions
            this.readDataTimer.Enabled = true;


        }

        #endregion Collect Data Constructor (Wockets, MITes, Builtin)

        #region Classifier constructor

        public void InitializeActivityTracker(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration)
        {
            this.storageDirectory = storageDirectory;
            this.wocketsController = wocketsController;
            this.annotatedSession = annotatedSession;
            this.classifierConfiguration = classifierConfiguration;

            //Initialize high resolution unix timer
            WocketsTimer.InitializeTime();

            //Initialize and start GUI progress thread
            progressMessage = null;
            aProgressThread = new Thread(new ThreadStart(ProgressThread));
            aProgressThread.Start();


            #region Initialize GUI Components
            //initialize the interface components
            InitializeComponent();
            //Initialize GUI timers
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing Timers ...";
            InitializeTimers();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\nInitializing GUI ...";
            InitializeInterface();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\n";
            this.isPlotting = true;

         
            aWocketsPlotter = new WocketsScalablePlotter(((Panel)this.panels[VISUALIZE_PANEL]), this.wocketsController);

            this.Resize += new EventHandler(OnResize);


            //Remove classifier tabs
            this.viewsMenu[1].Enabled = false;
            this.Text = "Activity Tracking";



            #endregion Initialize GUI Components

            #region Initialize Feature Extraction

            FeatureExtractor.Initialize(this.wocketsController, this.classifierConfiguration, this.annotatedSession.OverlappingActivityLists[0]);//this.masterDecoder, dataDirectory, this.annotation, this.sensors, this.configuration);
            #endregion Initialize Feature Extraction

            labelIndex = new Hashtable();
            //find arff file
        
            
            classifier = new J48();
            if (!File.Exists(this.storageDirectory + "\\model.xml"))
            {
                string[] arffFiles = Directory.GetFileSystemEntries(this.storageDirectory, "output*.arff");
                if (arffFiles.Length != 1)
                    throw new Exception("Multiple Arff Files in Directory");
                instances = new Instances(new StreamReader(arffFiles[0]));
                instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                classifier.buildClassifier(instances);
                TextWriter tc = new StreamWriter(this.storageDirectory + "\\model.xml");
                classifier.toXML(tc);
                tc.Flush();
                tc.Close();
            }
            else
            {
                instances = new Instances(new StreamReader(this.storageDirectory + "\\structure.arff"));
                instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                classifier.buildClassifier(this.storageDirectory + "\\model.xml", instances);
            }


            fvWekaAttributes = new FastVector(FeatureExtractor.ArffAttributeLabels.Length + 1);
            for (int i = 0; (i < FeatureExtractor.ArffAttributeLabels.Length); i++)
                fvWekaAttributes.addElement(new weka.core.Attribute(FeatureExtractor.ArffAttributeLabels[i]));

            FastVector fvClassVal = new FastVector();
            labelCounters = new int[this.annotatedSession.OverlappingActivityLists[0].Count + 1];
            activityLabels = new string[this.annotatedSession.OverlappingActivityLists[0].Count + 1];
            for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists[0].Count); i++)
            {
                labelCounters[i] = 0;
                string label = "";
                int j = 0;
                for (j = 0; (j < this.annotatedSession.OverlappingActivityLists.Count - 1); j++)
                    label += this.annotatedSession.OverlappingActivityLists[j][i]._Name.Replace(' ', '_') + "_";
                label += this.annotatedSession.OverlappingActivityLists[j][i]._Name.Replace(' ', '_');
                activityLabels[i] = label;
                labelIndex.Add(label, i);
                fvClassVal.addElement(label);
            }

            this.ActGUIlabels = new Label[activityLabels.Length];
            Label cur= new Label();
            cur = new Label();
            cur.Font = new System.Drawing.Font("Tahoma", 14F, System.Drawing.FontStyle.Bold);
            cur.Text = "Best Guess:";
            cur.Location = new Point(16, 16);
            cur.Size = new Size(400, 50);
            ((Panel)this.panels[CLASSIFIER_LABEL_PANEL]).Controls.Add(cur);
            Color blank = Color.FromArgb(240, 240, 240);
            for (int i = 0; i < activityLabels.Length; i++)
            {
                cur = new Label();
                cur.Font = new System.Drawing.Font("Tahoma", 14F, System.Drawing.FontStyle.Bold);
                cur.Text = activityLabels[i];
                cur.Location = new Point(16, 66 + i * 50);
                cur.Size= new Size(400,50);
                cur.ForeColor = blank;
                this.ActGUIlabels[i] = cur;
                ((Panel)this.panels[CLASSIFIER_LABEL_PANEL]).Controls.Add(cur);
            }

            weka.core.Attribute ClassAttribute = new weka.core.Attribute("activity", fvClassVal);


            #region Start Collecting Data


            //Terminate the progress thread
            progressThreadQuit = true;

            //Enable all timer functions
            this.readDataTimer.Enabled = true;
            //this.qualityTimer.Enabled = true;

            #endregion Start Collecting Data

        }
        #endregion Classifier constructor

        #region Initialization Methods

        //Initialize timers for the GUI interface
        public void InitializeTimers()
        {
            this.goodTimer = new ATimer(this, GOOD_TIMER);
            this.overallTimer = new ATimer(this, OVERALL_TIMER);
            this.activityTimer = new ATimer(this, ACTIVITY_TIMER);

        }
    
        #endregion Initialization Methods

        #region Exergame Constructor

        public void InitializeExergame(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration)
        {
            this.storageDirectory = storageDirectory;
            this.wocketsController = wocketsController;
            this.annotatedSession = annotatedSession;
            this.classifierConfiguration = classifierConfiguration;

            //Initialize high resolution unix timer
            WocketsTimer.InitializeTime();

            //Initialize and start GUI progress thread
            progressMessage = null;
            aProgressThread = new Thread(new ThreadStart(ProgressThread));
            aProgressThread.Start();

            //Initialize Plotting Thread
            aPlottingThread = new Thread(new ThreadStart(PlotWockets));
            //aSavingThread = new Thread(new ThreadStart(SaveWockets));
            //aPollingThread = new Thread(new ThreadStart(this.wocketsController.Poll));
            //aPollingThread.Priority = ThreadPriority.Highest; 
            //aInternalPollingThread = new Thread(new ThreadStart(PollInternal));

            //this.bluetoothControllers = new BluetoothController[this.wocketsController._Receivers.Count];
            // this.bluetoothConnectors = new BluetoothConnector[this.wocketsController._Receivers.Count];




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
            aWocketsPlotter = new WocketsScalablePlotter(((Panel)this.panels[VISUALIZE_PANEL]), this.wocketsController);

            //Override the resize event
            this.Resize += new EventHandler(OnResize);


            //Initialize the quality interface
           /* while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing MITes Quality GUI ...";
            InitializeQualityInterface();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\n";
            */

            //Remove classifier tabs
#if (PocketPC)

            //this.viewsMenu[2].Enabled = false;
            //this.viewsMenu[3].Enabled = false;
#else
            this.ShowForms();
#endif


            #endregion Initialize GUI Components

            #region Initialize Feature Extraction
            FeatureExtractor.Initialize(this.wocketsController, this.classifierConfiguration, this.annotatedSession.OverlappingActivityLists[0]);
            #endregion Initialize Feature Extraction

            #region Initialize Quality Tracking variables
            //InitializeQuality();
            #endregion Initialize Quality Tracking variables

            #region Initialize Logging
            //InitializeLogging(this.storageDirectory);
            #endregion Initialize Logging



            #region Bluetooth reception channels initialization
            //Initialize and search for wockets connections
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing receivers ... searching " + this.wocketsController._Receivers.Count + " BT receivers\r\n";

            this.wocketsController.Initialize();
            foreach (Decoder d in this.wocketsController._Decoders)
            {
                // d.Subscribe(SensorDataType.BATTERYLEVEL, new Response.ResponseHandler(this.BatteryCallback));
            }

            //Try to initialize all receivers 10 times then exit
            /*int initializationAttempt = 0;
            while (initializationAttempt <= 10)
            {
                Wockets.Data.Commands.BatteryResponse br = (Wockets.Data.Commands.BatteryResponse)e._Response;
                ((PictureBox)this.sensorBattery["W" + br.SensorID]).Image = this.batteryImg[(5*1024-5*br.BatteryLevel)/1024];
                
                updateCommand("Received Battery Response: "+br.BatteryLevel);
            }
             */
            #endregion Bluetooth reception channels initialization




            aPlottingThread.Start();
            //aSavingThread
            //aPollingThread.Start();
            //aInternalPollingThread.Start();
            //aSavingThread.Start();

            //Terminate the progress thread
            progressThreadQuit = true;

            //Enable all timer functions
            this.readDataTimer.Enabled = true;
    
            this.wocketsController._annotatedSession = this.annotatedSession;
            this.wocketsController._storageDirectory = this.storageDirectory;

        }

        #endregion Exergame Constructor





        #region Resize Event Handlers

        private void OnResize(object sender, EventArgs ee)
        {

            if ((this.Width > Constants.FORM_MIN_WIDTH) && (this.Height > Constants.FORM_MIN_HEIGHT))
            {


                ((Panel)this.panels[VISUALIZE_PANEL]).Width = this.ClientSize.Width;
                ((Panel)this.panels[VISUALIZE_PANEL]).Height = this.ClientSize.Height;


                //Intialize Labels 40% of the screen

                int num_rows = (int)((this.wocketsController._Sensors.Count + 2) / 2); //additional row for HR and total sampling rate
                int textBoxHeight = ((int)(0.40 * ((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
                int textBoxWidth = ((((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 3);
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

                for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
                {

                    string labelKey = "";

                    labelKey = "W" + this.wocketsController._Sensors[i]._ID;
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

                aWocketsPlotter = new WocketsScalablePlotter(((Panel)this.panels[VISUALIZE_PANEL]), this.wocketsController);

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
                    this.overallTimer.start();
                    activityList[j].BackColor = Color.SkyBlue;
                    selectedButtons.Remove(activityList[j]);
                }
                else if (index == j)
                {
                    activityList[j].BackColor = Color.DodgerBlue;
                    selectedButtons.Add(activityList[j]);
                }      
            }
                    
            
            
          /*  if (button.BackColor == clickColor)
            {
                button.BackColor = this.defaultColor;
                //selectedButtons.Remove(button);
            }
            else
            {
                button.BackColor = clickColor;
                //selectedButtons.Add(button);
            }*/

            if (this.currentRecord != null)
            {
                stopAnnotation();

                TextWriter tw = new StreamWriter(this.storageDirectory + "\\AnnotationIntervals.xml");                
                tw.WriteLine(this.annotatedSession.ToXML());                
                tw.Close();
            }
            if (selectedButtons.Count > 0)
                startAnnotation();  
        }


        ArrayList records = new ArrayList();

        private void startAnnotation()
        {
            this.currentRecord = new Annotation();
            this.currentRecord._StartDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            this.currentRecord._StartHour = DateTime.Now.Hour;
            this.currentRecord._StartMinute = DateTime.Now.Minute;
            this.currentRecord._StartSecond = DateTime.Now.Second;
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
        }

        private void stopAnnotation()
        {
            this.currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            this.currentRecord._EndHour = DateTime.Now.Hour;
            this.currentRecord._EndMinute = DateTime.Now.Minute;
            this.currentRecord._EndSecond = DateTime.Now.Second;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._EndUnix = ts.TotalSeconds;
            this.annotatedSession.Annotations.Add(this.currentRecord);
            this.currentRecord = null;
        }

        /*
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
                    foreach (ComboBox c in this.categoryDrops)
                        c.Enabled = false;
                    startAnnotation();
                    this.wocketsController._currentRecord = this.currentRecord;
                }

                else if (item.Text.Equals("Stop"))
                {
                    item.Text = "Start";
                    this.overallTimer.reset();
                    extractedVectors = 0;
                    stopAnnotation();
                    TextWriter tw = new StreamWriter(this.storageDirectory + "\\AnnotationIntervals.xml");
                    // write a line of text to the file
                    tw.WriteLine(this.annotatedSession.ToXML());
                    // close the stream
                    tw.Close();
                    foreach (ComboBox c in this.categoryDrops)
                        c.Enabled = true;                   
                }
                this.wocketsController._currentRecord = this.currentRecord;
                this.wocketsController._annotatedSession = this.annotatedSession;
            }
        }

        */

        private void startStopButton_Click(object sender, EventArgs e)
        {
            lock (WocketsController.MyLock)
            {
                MenuItem item = (MenuItem)sender;
                //button state is now start
                if (item.Text.Equals("Start"))
                {
                    // this.startSound.Play();
                    //Generator generator = new Generator();
                    //generator.InitializeSound(this.Handle.ToInt32());
                    //generator.CreateBuffer();

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
                    this.wocketsController._currentRecord = this.currentRecord;
                }

                else if (item.Text.Equals("Stop"))
                {
                    // this.stopSound.Play();
                    item.Text = "Start";
                    this.overallTimer.reset();
                    this.goodTimer.reset();
                    extractedVectors = 0;

                    //store the current state of the categories
                    this.currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                    this.currentRecord._EndHour = DateTime.Now.Hour;
                    this.currentRecord._EndMinute = DateTime.Now.Minute;
                    this.currentRecord._EndSecond = DateTime.Now.Second;
                    TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                    this.currentRecord._EndUnix = ts.TotalSeconds;
                    this.annotatedSession.Annotations.Add(this.currentRecord);

                    //each time an activity is stopped, rewrite the file on disk, need to backup file to avoid corruption
                    //this.annotation.ToXMLFile();
                    //this.annotation.ToCSVFile();
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
                    this.wocketsController._currentRecord = this.currentRecord;
                }
                this.wocketsController._annotatedSession = this.annotatedSession;
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

        private void training_Click(object sender, EventArgs e)
        {
            MenuItem mi = (MenuItem)sender;
            mi.Checked = !(mi.Checked);
            this.isTraining = mi.Checked;
            this.wocketsController.Training = this.isTraining;
        }

        private void classifying_Click(object sender, EventArgs e)
        {
            MenuItem mi = (MenuItem)sender;
            mi.Checked = !(mi.Checked);

            classifier = new J48();
            if (!File.Exists(this.storageDirectory + "\\model.xml"))
            {
                string[] arffFiles = Directory.GetFileSystemEntries(this.storageDirectory, "output*.arff");
                if (arffFiles.Length != 1)
                    throw new Exception("Multiple Arff Files in Directory");
                instances = new Instances(new StreamReader(arffFiles[0]));
                instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                classifier.buildClassifier(instances);
                TextWriter tc = new StreamWriter(this.storageDirectory + "\\model.xml");
                classifier.toXML(tc);
                tc.Flush();
                tc.Close();
            }
            else
            {
                instances = new Instances(new StreamReader(this.storageDirectory + "\\structure.arff"));
                instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                classifier.buildClassifier(this.storageDirectory + "\\model.xml", instances);
            }

            fvWekaAttributes = new FastVector(FeatureExtractor.ArffAttributeLabels.Length + 1);
            for (int i = 0; (i < FeatureExtractor.ArffAttributeLabels.Length); i++)
                fvWekaAttributes.addElement(new weka.core.Attribute(FeatureExtractor.ArffAttributeLabels[i]));

            this.isClassifying = mi.Checked;
            this.wocketsController._Classifying = this.isClassifying;
            this.wocketsController._instances = this.instances;
            this.wocketsController._classifier = this.classifier;
        }

        private void gaming_Click(object sender, EventArgs e)
        {
            MenuItem mi = (MenuItem)sender;
            mi.Checked = !(mi.Checked);
            this.isGaming = mi.Checked;
            Thread aGamingThread = new Thread(new ThreadStart(this.wocketsController._Escape.PlayExergame));
            this.wocketsController._Escape.isGaming = this.isGaming;
            aGamingThread.Start();
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
            if (this.mainMenu1.MenuItems.Contains(this.menuItem15))
                this.mainMenu1.MenuItems.Remove(this.menuItem15);
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
                        this.mainMenu1.MenuItems.Add(this.menuItem15);     
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
                this.mainMenu1.MenuItems.Add(this.menuItem15);
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
                String excp = "";
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
                    this.label1.Text = this.wocketsController.extractedVectors.ToString();

                    this.label3b.Text = label;
                    this.label1b.Text = extractedVectors.ToString();

                }
#if (PocketPC)
                else if (control_id == ACTIVITY_TIMER)
                {
                    pieChart.SetTime(label);
                    pieChart.Invalidate();
                }
#endif
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

            //if (this.CurrentPanel == 0)
            if (((Panel)this.panels[VISUALIZE_PANEL]).Visible)
            {


                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);


            }

        }



 
        #endregion Graphing functions


        #region Timer Methods






        #region Builtin Accelerometr Polling Thread
#if (PocketPC)

#endif
        #endregion Builtin Accelerometr Polling Thread

        private bool isTraining = false;
        private bool isClassifying = false;
        private bool isGaming = false;
        private TextWriter trainingTW = null;
        private TextWriter structureTW = null;

        private int extractedVectors = 0;
   

        [DllImport("coredll.dll", SetLastError = true)]
        public static extern int CeGetThreadQuantum(IntPtr handle);

        [DllImport("coredll.dll", SetLastError = true)]
        public static extern int CeSetThreadQuantum(IntPtr handle,ushort dw);


        private void PlotWockets()
        {
            while (true)
            {
                if (isPlotting)
                    UpdateGraph();
            
                Thread.Sleep(50);
            }
        }


        int sound_timer = 0;
        private void readDataTimer_Tick(object sender, EventArgs e)
        {
                        
            for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
            {
                if ( (this.wocketsController._Receivers[i]._Status== ReceiverStatus.Disconnected) ||
                    (this.wocketsController._Receivers[i]._Status== ReceiverStatus.Reconnecting))
                {
                    if (this.wocketsController._Receivers[i].Disconnected >= 1000)
                    {
                        if (sound_timer > 150)
                        {
                            alert.Play();                            
                            sound_timer = 0;
                        }
                        else
                            sound_timer++;
                    }
                    else
                        this.wocketsController._Receivers[i].Disconnected += 1;
                }
                else
                    this.wocketsController._Receivers[i].Disconnected = 0;                
            }



            this.SRcounter++;

            if (this.SRcounter > 1600)//Update status interface every 5 minutes
            {
                String log="";
                int disc;
                int time;
                String report;
                long now = DateTime.Now.Ticks;
                for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
                {
                    disc = this.wocketsController._Receivers[i].NumDisconnect;
                    time = this.wocketsController._Receivers[i].TimeDisconnect;
                    this.wocketsController._Receivers[i].NumDisconnect = 0;
                    this.wocketsController._Receivers[i].TimeDisconnect = 0;
                    report = "Sensor " + this.wocketsController._Sensors[i]._ID + ": " + this.wocketsController._Sensors[i].Packets / ((now - this.LastTime) / 10000000) + ", " + disc + ", " + time; 
                    this.SampLabels[i].Text = report;
                    log += report + "\n";
                    this.wocketsController._Sensors[i].Packets = 0;
                }

                Logger.Warn(log);
                this.SRcounter = 0;
                this.LastTime = now;
                

            }
            
            if (isQuitting)
            {
                this.alert.Stop();

                this.wocketsController.Dispose();

                Logger.Close();

                FeatureExtractor.Cleanup();
                
                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();

            }             

        }
        private void updateCommand(string s)
        {
            this.CommandBox.Text += s+"\r\n";
            this.CommandBox.SelectionStart = this.CommandBox.Text.Length;
            this.CommandBox.ScrollToCaret();
        }



        delegate void UpdateGraphCallback();
        public void UpdateGraph()
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

                for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
                {
                    String key = "W" + this.wocketsController._Receivers[i]._ID;
                    if (this.wocketsController._Receivers[i]._Status== ReceiverStatus.Connected)
                        ((PictureBox)this.sensorStatus[key]).Image = (Image)this.connectedWocketImage;
                    else
                        ((PictureBox)this.sensorStatus[key]).Image = (Image)this.disconnectedWocketImage;

                }

                if  (isPlotting)
                {
                    GraphAccelerometerValues();
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
                ((PictureBox)this.sensorBattery["W" + br.SensorID]).Image = this.batteryImg[(5*1024-5*br.BatteryLevel)/1024];                
                updateCommand("Received Battery Response: "+br.BatteryLevel);
            }
        }

    }
}