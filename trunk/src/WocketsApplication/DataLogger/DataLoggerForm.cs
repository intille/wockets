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
#if (PocketPC)
using WocketsApplication.Feedback;
#endif


namespace WocketsApplication.DataLogger
{
    public partial class DataLoggerForm : Form, SetTextControlCallback
    {
        #region Declarations of Objects

        #region Definition of Plotting and Graphing Variables

        private bool isResized = false;

        private bool isPlotting = false;
        private Bitmap backBuffer = null;
        private WocketsScalablePlotter aWocketsPlotter;
        private Pen aPen = new Pen(Color.Wheat);
        private SolidBrush aBrush = new SolidBrush(Color.White);
        private SolidBrush blueBrush = new SolidBrush(Color.LightBlue);
        private SolidBrush redBrush = new SolidBrush(Color.Red);


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
        /// <summary>
        /// Delegate that sets the graphics for the signal strength from other threads
        /// </summary>
        /// <param name="isGood">True if signal is good otherwise false</param>
        delegate void SetSignalCallback(bool isGood);
        /// <summary>
        /// Delegate that sets an error label from different threads (e.g. used to display bluetooth disconnection)
        /// </summary>
        /// <param name="label"></param>
        delegate void SetErrorCallback(string label);
        #endregion GUI Delegates

        #region Definition of GUI Components
        /// <summary>
        /// A hashtable for the labels of different snesors
        /// </summary>
        private Hashtable sensorLabels;
        private Hashtable sensorStatus;
        private Hashtable sensorBattery;
        private Hashtable mainMenus;
        private Panel[] panelArray;
        private Panel[] annotatePanelArray;
        private MenuItem[] viewsMenu = new MenuItem[6];
        private MenuItem[] annotateViewsMenu = new MenuItem[2];
        private int panelSwitch = 0;
        
        private Image[] batteryImg = new Image[] { (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "1.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "2.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "3.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "4.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "5.gif"), (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "6.gif") };
        private Label samplingLabel;
        private System.Windows.Forms.Label[] labels;
        /// <summary>
        /// Expected sampling rate labels
        /// </summary>
        private System.Windows.Forms.Label[] expectedLabels;
        /// <summary>
        /// Samples per second labels
        /// </summary>
        private System.Windows.Forms.Label[] samplesPerSecond;
        /// <summary>
        /// The message to be displayed by the progress thread
        /// </summary>
        private string progressMessage;
        /// <summary>
        /// The progress thread object
        /// </summary>
        private Thread aProgressThread = null;

        private Thread aPlottingThread = null;//aPollingThread = null;
        //private Thread aInternalPollingThread = null;
        private Thread aSavingThread = null;

        /// <summary>
        /// True if the progress thread should quit
        /// </summary>
        private bool progressThreadQuit = false;
        /// <summary>
        /// An array list of the different buttons of the annotator
        /// </summary>
        private ArrayList categoryButtons;
        /// <summary>
        /// An array list that stores the current index for each button
        /// </summary>
        private ArrayList categoryDrops;
        private ArrayList buttonIndex;
        /// <summary>
        /// A variable that stores the longest label on a category button for dynamic resizing of the buttons
        /// </summary>
        private string longest_label = "";
        private int label_width;
        private int label_height;
        private Font textFont;

        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
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

        #region Definition of Logging Variables and Flags
        /// <summary>
        /// A constant that specifies how often to flush logging data
        /// </summary>
        private const int FLUSH_TIMER_MAX = 6000;

        private Sound alert = new Sound(Constants.NEEDED_FILES_PATH + "sounds\\stop.wav");
        private bool play_sound = false;

        #endregion Definition of Logging Variables and Flags

        #region Wockets and MITes Variables

        #region Definitions of general configuration variables



        /// Directory where the collected data will be stored
        /// </summary>
        private string dataDirectory;
        //TODO: move it to configuration file
        /// <summary>
        /// Defines the buffer size for different controllers - expanded for wockets
        /// </summary>
        private const int BYTES_BUFFER_SIZE = 4096; //2048      

        #endregion Definitions of general configuration variables

        #region Definition of controllers for different reception channels
        //TODO: Define a single interface for ReceiverController and extend it to use USB,Bluetooth or DiamondTouch
        //  private MITesReceiverController[] mitesControllers;
#if (PocketPC)
        //private BluetoothController[] bluetoothControllers;
        private BluetoothConnector[] bluetoothConnectors;

#endif
        #endregion Definition of controllers for different reception channels



        #region Definition of performance objects and counters



        #endregion Definition of performance objects and counters

        #region Definition of logging functions
        //private MITesLoggerPLFormat aPLFormatLogger;
        //private PLFormatLogger aPLFormatLogger;
        //private MITesActivityLogger aMITesActivityLogger;
        #endregion Definition of logging functions

        #region Definition of built-in sensors polling threads   (Pocket PC Only)
#if (PocketPC)
        /// <summary>
        /// Counter for the next polling time for the built-in accelerometer
        /// </summary>
        private int pollingTime = Environment.TickCount;
  
#endif
        #endregion Definition of built-in sensors polling threads   (Pocket PC Only)

        #endregion Wockets and MITes Variables

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
        private Annotation currentRecord;

        #endregion Definition of annotation objects

#if (PocketPC)
        [DllImport("coredll.dll")]
        public static extern int PlaySound(
            string szSound,
            IntPtr hModule,
            int flags);
#endif

        #endregion Declarations of Objects

        public DataLoggerForm(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration, int mode)
        {
            Logger.InitLogger(storageDirectory);
            this.LastTime = this.FirstTime = DateTime.Now.Ticks;
            if (mode == 1)
                InitializeAnnotator(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 2)
                InitializeDataLogger(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 3)
                InitializeActivityTracker(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
           

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

            //Initialize where the data will be stored and where the configuration
            //files exist
            this.dataDirectory = "\\Wockets";


            //load the activity and sensor configuration files



            InitializeTimers();

            //Initialize different GUI components
            InitializeInterface();
            //Initialize the timers




#if (PocketPC)

#endif

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
#if (PocketPC)
                Thread.Sleep(5);
#else
                Thread.Sleep(20);
#endif

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
            aWocketsPlotter = new WocketsScalablePlotter(this.panel1, this.wocketsController);

            //Override the resize event
            this.Resize += new EventHandler(OnResize);


            //Initialize the quality interface
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing MITes Quality GUI ...";
            InitializeQualityInterface();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\n";

            //Remove classifier tabs
#if (PocketPC)

            this.viewsMenu[2].Enabled = false;
            this.viewsMenu[3].Enabled = false;
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
                d.Subscribe(SensorDataType.BATTERYLEVEL, new Response.ResponseHandler(this.BatteryCallback));
            }
            //Try to initialize all receivers 10 times then exit
            /*int initializationAttempt = 0;
            while (initializationAttempt <= 10)
            {
                if (InitializeReceivers() == false)
                {
                    initializationAttempt++;

                    if (initializationAttempt == 10)
                    {
                        MessageBox.Show("Exiting: Some receivers in your configuration were not initialized.");
                        Application.Exit();
                        System.Diagnostics.Process.GetCurrentProcess().Kill();
                    }
                    else
                    {
                        while (progressMessage != null) Thread.Sleep(50);
                        progressMessage = "Failed to initialize some receivers. Retrying (" + initializationAttempt + ")...\r\n";
                    }

                }
                else
                    break;

                //we noticed that without the delay the BT stack might fail to connect to all of them. Spacing them out is a good idea
                
                Thread.Sleep(500);
            }
             */
            #endregion Bluetooth reception channels initialization

            /*
            #region Start Collecting Data

            Receiver currentReceiver = null;
            Sensor sensor = null;
         
                //Cleanup receiver buffers as they are out of sync due to BT connection delays
                //set them to saving mode
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                try
                {
                    sensor = this.wocketsController._Sensors[i];
                    sensor._Saving = true;
                    currentReceiver = this.wocketsController._Receivers[sensor._Receiver];
//                    if (currentReceiver._Running == true)
 //                       currentReceiver.Read();
                }
                catch (Exception e)
                {
                    ((PictureBox)this.sensorStatus["W" + sensor._ID]).Image = disconnectedWocketImage;
                    this.bluetoothConnectors[currentReceiver._ID] = new BluetoothConnector(currentReceiver, this.wocketsController);
                    currentReceiver._Running = false;
                }
            }

            */


            aPlottingThread.Start();
            //aSavingThread
            //aPollingThread.Start();
            //aInternalPollingThread.Start();
            //aSavingThread.Start();

            //Terminate the progress thread
            progressThreadQuit = true;

            //Enable all timer functions
            this.readDataTimer.Enabled = true;
            //this.qualityTimer.Enabled = true;



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

            //this.bluetoothControllers = new BluetoothController[this.wocketsController._Receivers.Count];
            this.bluetoothConnectors = new BluetoothConnector[this.wocketsController._Receivers.Count];
            for (int i = 0; i < this.wocketsController._Receivers.Count; i++)
            {
                this.bluetoothConnectors[i] = null;
            }

            #region Bluetooth reception channels initialization
            //Initialize and search for wockets connections
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing Bluetooth receivers ... searching " + this.wocketsController._Receivers.Count + " BT receivers\r\n";

            //Try to initialize all Bluetooth receivers 10 times then exit
            int initializationAttempt = 0;
            while (initializationAttempt <= 10)
            {
                if (InitializeReceivers() == false)
                {
                    initializationAttempt++;

                    if (initializationAttempt == 10)
                    {
                        MessageBox.Show("Exiting: Some Bluetooth receivers in your configuration were not initialized.");
                        Application.Exit();
                        System.Diagnostics.Process.GetCurrentProcess().Kill();
                    }
                    else
                    {
                        while (progressMessage != null) Thread.Sleep(50);
                        progressMessage = "Failed to initialize all BT connections. Retrying (" + initializationAttempt + ")...\r\n";
                    }

                }
                else
                    break;
                Thread.Sleep(2000);
            }
            #endregion Bluetooth reception channels initialization


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

            //SetFormPositions();            
            aWocketsPlotter = new WocketsScalablePlotter(this.panel1, this.wocketsController);

            this.Resize += new EventHandler(OnResize);


            //Initialize the quality interface
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing MITes Quality GUI ...";
            InitializeQualityInterface();
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\n";

            //Remove classifier tabs
            this.viewsMenu[1].Enabled = false;
#if (PocketPC)

            this.Text = "Activity Tracking";
#else
            this.ShowForms();
#endif


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
            this.panel4.Controls.Add(cur);
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
                this.panel4.Controls.Add(cur);
            }

            weka.core.Attribute ClassAttribute = new weka.core.Attribute("activity", fvClassVal);

            #region Initialize Quality Tracking variables
            //InitializeQuality();
            #endregion Initialize Quality Tracking variables

            #region Initialize Logging
            //InitializeLogging(this.storageDirectory);
            #endregion Initialize Logging

            #region Start Collecting Data

            Receiver currentReceiver = null;
            Sensor sensor = null;
            try
            {
                //Cleanup receiver buffers as they are out of sync due to BT connection delays
                for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
                {
                    sensor = this.wocketsController._Sensors[i];
                    currentReceiver = sensor._Receiver;
 //                   if (currentReceiver._Running == true)
 //                       currentReceiver.Read();
                }
            }
            catch (Exception e)
            {
                ((PictureBox)this.sensorStatus["W" + sensor._ID]).Image = disconnectedWocketImage;
                this.bluetoothConnectors[currentReceiver._ID] = new BluetoothConnector(currentReceiver, this.wocketsController);
                currentReceiver._Running = false;
            }

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



#if (PocketPC)
        //Initialize Bluetooth receiver channels includes wockets, sparkfun, Bluetooth enabled MITes
        private bool InitializeReceivers()
        {
            //Initialize all defined reception channels Bluetooth
            //foreach (Receiver receiver in this.sensors.Receivers)
            for (int i = 0; (i < this.wocketsController._Receivers.Count); i++)
            {
                //If reception channel is of type Bluetooth and is not already initialized
                if (this.wocketsController._Receivers[i]._Running == false)
                {
                    //Create a Bluetooth controller
                    while (progressMessage != null) Thread.Sleep(50);
                    if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                        progressMessage = "Initializing Bluetooth for " + ((RFCOMMReceiver)this.wocketsController._Receivers[i])._Address + " ...\r\n";
                    else if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.HTCDiamond)
                        progressMessage = "Initializing HTC Diamond ...\r\n";
                    //this.bluetoothControllers[this.wocketsController._Receivers[i]._ID] = new BluetoothController();
                    try
                    {
                        this.wocketsController._Receivers[i].Initialize();
                    }
                    catch (Exception e)
                    {
                        while (progressMessage != null) Thread.Sleep(50);
                        if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                            progressMessage = "Failed to find" + ((RFCOMMReceiver)this.wocketsController._Receivers[i])._Address + " ...\r\n";
                        else if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.HTCDiamond)
                            progressMessage = "Failed to initialize HTC Diamond ...\r\n";
                        return false;
                    }
     
                    //this.wocketsController._Receivers[i]._Running = true;
                }

            }

            return true;
        }

#endif





        //Initialize objects for logging and storing wockets and MITes data
        /*private void InitializeLogging(string dataDirectory)
        {

            aPLFormatLogger = new PLFormatLogger(this.wocketsController,
                                                         dataDirectory + "\\data\\raw\\PLFormat\\");
        }*/
    
        #endregion Initialization Methods







        #region Resize Event Handlers

        private void OnResize(object sender, EventArgs ee)
        {

            if ((this.Width > Constants.FORM_MIN_WIDTH) && (this.Height > Constants.FORM_MIN_HEIGHT))
            {

                //this.tabControl1.Width = this.ClientSize.Width;
               // this.tabControl1.Height = this.ClientSize.Height;
                this.panel1.Width = this.ClientSize.Width;
                this.panel1.Height = this.ClientSize.Height;


                //Intialize Labels 40% of the screen

                int num_rows = (int)((this.wocketsController._Sensors.Count + 2) / 2); //additional row for HR and total sampling rate
                int textBoxHeight = ((int)(0.40 * this.panel1.ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
                int textBoxWidth = ((this.panel1.ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 3);
                int currentTextY = (int)(this.panel1.ClientSize.Height * 0.60);
                int leftTextX = Constants.WIDGET_SPACING + 32;
                int rightTextX = ((Constants.WIDGET_SPACING + 32) * 2) + textBoxWidth;
                int currentTextX = Constants.WIDGET_SPACING + 32;
                this.button1.Width = textBoxWidth;
                this.button1.Height = textBoxHeight;

                Font textFont;


                textFont = this.button1.Font =
                GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.button1.Size, "textBoxAC11", this.button1.Font, (float)0.9, (float)0.9);

                System.Windows.Forms.Label t;
                //foreach (Sensor sensor in this.sensors.Sensors)
                for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
                {

                    string labelKey = "";
                 
                    labelKey = "W" + this.wocketsController._Sensors[i]._ID;                       
                    PictureBox p= (PictureBox)this.sensorStatus[labelKey];                       
                    p.Location = new System.Drawing.Point(currentTextX-33, currentTextY);
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




                t = (System.Windows.Forms.Label)this.sensorLabels["SampRate"];
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


                //Initialize Buttons
                int button_width = this.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
                int button_height = (this.ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - (this.annotatedSession.OverlappingActivityLists.Count * Constants.WIDGET_SPACING)) / (this.annotatedSession.OverlappingActivityLists.Count + 1);
                int button_x = Constants.WIDGET_SPACING;
                int button_y = Constants.WIDGET_SPACING * 2;

                int delta_y = button_height + Constants.WIDGET_SPACING;
                int button_id = 0;


                this.button1.Width = button_width;
                this.button1.Height = button_height;
                Font buttonFont = this.button1.Font =
                    GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.button1.Size, longest_label, this.button1.Font, (float)0.9, (float)0.9);

                foreach (System.Windows.Forms.Button button in categoryButtons)
                {
                    button.Location = new System.Drawing.Point(button_x, button_y + button_id * delta_y);
                    button.Font = buttonFont;
                    button.Size = new System.Drawing.Size(button_width, button_height);
                    button_id++;
                }

                //adjust round buttons start/stop -reset
                button_width = (this.Size.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 2;

                //adjust the size of the plotter
                //if (this.sensors.TotalReceivers>0)
                //aWocketsPlotter = new WocketsScalablePlotter(this.panel1, WocketsScalablePlotter.DeviceTypes.IPAQ, maxPlots,this.wocketsController, new Size(this.panel1.Width, (int)(0.60 * this.panel1.Height)));
                aWocketsPlotter = new WocketsScalablePlotter(this.panel1, this.wocketsController);
                //else
                //  aWocketsPlotter = new WocketsScalablePlotter(this.panel1, WocketsScalablePlotter.DeviceTypes.IPAQ, maxPlots, this.masterDecoder, new Size(this.panel1.Width, (int)(0.60 * this.panel1.Height)));
                //SetFormPositions();
                this.isResized = true;
            }
        }

        #endregion Resize Event Handlers

        #region Click Event Handlers

        //Click end training
        void menuItem6Tab2_Click(object sender, EventArgs e)
        {
            EndTraining();
            this.overallTimer.reset();
            this.goodTimer.reset();
        }

        //Start a training session
        void menuItem5Tab2_Click(object sender, EventArgs e)
        {
            /*
            this.arffFileName = this.dataDirectory + "\\output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";
            tw = new StreamWriter(arffFileName);
            if (AutoTraining == true)
            {
                int i = 0;
                tw.WriteLine("@RELATION wockets");
                tw.WriteLine(FeatureExtractor.GetArffHeader());
                tw.Write("@ATTRIBUTE activity {");
                for (i = 0; (i < ((this.annotatedSession.OverlappingActivityLists[0]).Count - 1)); i++)
                    tw.WriteLine(this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + ",");
                tw.WriteLine(this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + "}");
                tw.WriteLine("\n@DATA\n\n");

            }

            this.menuItem5Tab2.Checked = true;
            this.menuItem5Tab2.Enabled = false;

            if (this.menuItem8Tab2.Checked == true) // manual, you can end it
                this.menuItem6Tab2.Enabled = true;

            //cannot change the traing mode if a session started
            this.menuItem8Tab2.Enabled = false;
            this.menuItem7Tab2.Enabled = false;

            //enable stop/start and reset buttons
            this.startStopButton.Enabled = true;
            this.resetButton.Enabled = true;
            if (AutoTraining == true)
            {
                this.startStopButton.Enabled = false;
                this.resetButton.Enabled = false;
                ((Button)this.categoryButtons[0]).Enabled = false;
                ((Button)this.categoryButtons[0]).Visible = false;

                //temporary label for auto training

                if (this.trainingLabel == null)
                {

                    this.trainingLabel = new System.Windows.Forms.Label();
                    this.trainingLabel.Location = new Point(((Button)this.categoryButtons[0]).Location.X, ((Button)this.categoryButtons[0]).Location.Y);
                    this.trainingLabel.Size = new Size(((Button)this.categoryButtons[0]).Size.Width, ((Button)this.categoryButtons[0]).Size.Height);
                    this.trainingLabel.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
                    this.panel2.Controls.Add(trainingLabel);
                }

                this.trainingLabel.Visible = true;

                //this.autoTrainingIndex = 0;
                this.startActivityTime = Environment.TickCount + this.classifierConfiguration._TrainingWaitTime * 1000;
            }

            this.overallTimer.start();

            */
        }

        //Select manual mode session
        void menuItem8Tab2_Click(object sender, EventArgs e)
        {
            if (this.annotatedSession.OverlappingActivityLists.Count == 1)
            {
                this.menuItem8Tab2.Checked = true;
                this.menuItem8Tab2.Enabled = false;
                this.menuItem7Tab2.Checked = false;
                this.menuItem7Tab2.Enabled = true;
            }
        }

        //select auto mode session
        void menuItem7Tab2_Click(object sender, EventArgs e)
        {
            if (this.annotatedSession.OverlappingActivityLists.Count == 1)
            {
                this.menuItem7Tab2.Checked = true;
                this.menuItem7Tab2.Enabled = false;
                this.menuItem8Tab2.Checked = false;
                this.menuItem8Tab2.Enabled = true;
            }
        }

        private void oxycon_Click(object sender, EventArgs e)
        {
            DateTime now = DateTime.Now;
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
            TimeSpan diff = now.Subtract(origin);
            string timestamp = diff.TotalMilliseconds + "," + now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            TextWriter tw = new StreamWriter(this.dataDirectory + "\\OxyconSyncronizationTime.txt");
            tw.WriteLine(timestamp);
            tw.Close();
            this.oxyconButton.Enabled = false;
        }
        private void button2_Click(object sender, EventArgs e)
        {


        }


        private void button_Click(object sender, EventArgs e)
        {
            Button button = (Button)sender;
            int button_id = Convert.ToInt32(button.Name);
            ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
            int nextIndex = ((int)this.buttonIndex[button_id] + 1) % category.Count;
            button.Text = category[nextIndex]._Name;
            this.buttonIndex[button_id] = nextIndex;
        }

        ArrayList selectedButtons = new ArrayList();
        char[] delimiter ={ '_' };

        private void activityButton_Click(object sender, EventArgs e)
        {
            Button button = (Button)sender;
            int i = 0;
            Boolean same = false;

            while (i < selectedButtons.Count)
            {
                System.Windows.Forms.Button but = (System.Windows.Forms.Button)selectedButtons[i];
                if ((but.Name.Split(delimiter)[0]).Equals(button.Name.Split(delimiter)[0]))
                {
                    if (but.Equals(button))
                        same = true;
                    but.BackColor = this.defaultColor;
                    selectedButtons.RemoveAt(i);
                }
                i += 1;
            }

            if (!same)
            {
                button.BackColor = clickColor;
                selectedButtons.Add(button);
            }
        }


        private void startStopButton_Click(object sender, EventArgs e)
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
                if (this.panel2.Visible)
                {
                    foreach (ComboBox combo in categoryDrops)
                    {
                        int button_id = Convert.ToInt32(combo.Name);
                        ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                        string current_label = (string)combo.SelectedItem;
                        this.currentRecord.Activities.Add(new Activity(current_label, category._Name));
                        combo.Enabled = false;
                    }
                }
                else if (this.panel6.Visible)
                {
                    for (int i = 0; i < selectedButtons.Count; i++)
                    {
                        System.Windows.Forms.Button but = (System.Windows.Forms.Button)selectedButtons[i];
                        this.currentRecord.Activities.Add(new Activity(but.Name.Split(delimiter)[1], but.Name.Split(delimiter)[0]));
                    }
                    this.panel6.Enabled = false;
                }

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
                
                foreach (ComboBox c in this.categoryDrops)
                    c.Enabled = true;
                


                if (this.panel6.Visible)
                    this.panel6.Enabled = true;

                this.currentRecord = null;
            }
        }

        private void resetButton_Click(object sender, EventArgs e)
        {
            //this.resetSound.Play();
            //this.overallTimer.stop();
            this.overallTimer.reset();
            this.goodTimer.reset();

            foreach (Button category_button in categoryButtons)
            {
                int button_id = Convert.ToInt32(category_button.Name);
                ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                this.buttonIndex[button_id] = 0;
                category_button.Text = category[0]._Name;
                category_button.Enabled = true;
            }
        }

        private void menuItem13_Click(object sender, EventArgs e)
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
        }

        private void view_menu_Click(object sender, EventArgs e)
        {
            if (!((MenuItem)sender).Checked)
            {
                if (this.mainMenu1.MenuItems.Contains(this.menuItem15))
                {
                    this.mainMenu1.MenuItems.Remove(this.menuItem15);
                    this.mainMenu1.MenuItems.Add(this.menuItem2);
                }

                for (int i = 0; i < viewsMenu.Length; i++)
                {
                    if (this.viewsMenu[i].Checked)
                    {
                        this.viewsMenu[i].Checked = false;
                        this.panelArray[i].Visible = false;

                        break;
                    }

                }
                ((MenuItem)sender).Checked = true;
                for (int i = 0; i < viewsMenu.Length; i++)
                {
                    if (this.viewsMenu[i].Checked && !this.viewsMenu[i].Text.Equals("Annotate"))
                    {
                        this.panelArray[i].Visible = true;
                        for (int j = 0; j < annotateViewsMenu.Length; j++)
                        {
                            annotateViewsMenu[j].Checked = false;
                            annotatePanelArray[j].Visible = false;
                        }
                        break;
                    }
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

                for (int i = 0; i < viewsMenu.Length; i++)
                {
                    if (this.viewsMenu[i].Checked)
                        this.viewsMenu[i].Checked = false;
                    if (this.panelArray[i].Visible)
                        this.panelArray[i].Visible = false;
                }
                /*       try
                       {
                           this.viewsMenu[2].Checked = true;
                       }
                       catch (Exception ex) { excp = ex.ToString(); }
                 */
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


        private void menuItem1_Click(object sender, EventArgs e)
        {
#if (PocketPC)
            if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
#else
            if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo) == DialogResult.Yes)
#endif
            {
                isQuitting = true;

            }



        }


        private void menuItem22_Click(object sender, EventArgs e)
        {

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

        //close the ARFF training file and reset menus
        public void EndTraining()
        {
            this.menuItem6Tab2.Enabled = false;
            this.menuItem5Tab2.Checked = false;
            this.menuItem5Tab2.Enabled = true;

            if (this.annotatedSession.OverlappingActivityLists.Count == 1) //if 1 category
            {
                //enable whatever was not chosen to allow the user to switch the training mode
                if (this.menuItem8Tab2.Checked)
                    this.menuItem7Tab2.Enabled = true;
                else
                    this.menuItem8Tab2.Enabled = true;
            }
            ((Button)this.categoryButtons[0]).Visible = true;
            ((Button)this.categoryButtons[0]).Enabled = true;
        }

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
                //if (control_id == GOOD_TIMER)
                 //   this.label1.Text = label;
                if (control_id == OVERALL_TIMER)
                {
                    this.label3.Text = label;
                    this.label1.Text = extractedVectors.ToString();

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


        public void SetErrorLabel(string label)
        {
            // InvokeRequired required compares the thread ID of the
            // calling thread to the thread ID of the creating thread.
            // If these threads are different, it returns true.
            if (((System.Windows.Forms.Label)this.sensorLabels["ErrorLabel"]).InvokeRequired)
            {
                SetErrorCallback d = new SetErrorCallback(SetErrorLabel);
                this.Invoke(d, new object[] { label });
            }
            else
            {
                ((System.Windows.Forms.Label)this.sensorLabels["ErrorLabel"]).Text = label;
                ((System.Windows.Forms.Label)this.sensorLabels["ErrorLabel"]).Refresh();
            }
        }

        public void SetSignalSign(bool isGood)
        {
            // InvokeRequired required compares the thread ID of the
            // calling thread to the thread ID of the creating thread.
            // If these threads are different, it returns true.
            if (this.pictureBox1.InvokeRequired)
            {
                SetSignalCallback d = new SetSignalCallback(SetSignalSign);
                this.Invoke(d, new object[] { isGood });
            }
            else
            {
                //set the sign + control the good/bad timer
                /*if (isGood)
                {
                    if (this.startStopButton.BackColor == System.Drawing.Color.Red)
                        this.goodTimer.start();
                }
                else
                {
                    if (this.startStopButton.BackColor == System.Drawing.Color.Red)
                        this.goodTimer.stop();
                }*/
            }
        }




        #endregion Helper Methods






#if (!PocketPC)
        void form_FormClosing(object sender, FormClosingEventArgs e)
        {
            if (isQuitting == false)
                e.Cancel = true;
        }

#endif



#if (PocketPC)
#else
        public void ShowForms()
        {
            this.form1.Show();
            this.form2.Show();
            this.form3.Show();
            this.form4.Show();
            //this.form5.Show();
            this.form1.DesktopLocation = this.form1.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
            this.form3.DesktopLocation = this.form3.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + Constants.WIDGET_SPACING + this.form1.Height);
            this.form2.DesktopLocation = this.form2.Location = new Point(Constants.WIDGET_SPACING + Constants.WIDGET_SPACING + this.form1.Width, Constants.WIDGET_SPACING);
            this.form4.DesktopLocation = this.form4.Location = new Point(Constants.WIDGET_SPACING + Constants.WIDGET_SPACING + this.form1.Width, Constants.WIDGET_SPACING + Constants.WIDGET_SPACING + this.form2.Height);

        }
#endif


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
                backBuffer = new Bitmap(this.panel1.Width, (int)(this.panel1.Height*0.60));
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
#if (PocketPC)
            if (this.CurrentPanel == 0)
            {
#endif

                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);

#if (PocketPC)
            }
#endif
        }



 
        #endregion Graphing functions


        #region Timer Methods






        #region Builtin Accelerometr Polling Thread
#if (PocketPC)

#endif
        #endregion Builtin Accelerometr Polling Thread

        private bool isTraining = false;
        private TextWriter trainingTW = null;
        private TextWriter structureTW = null;

        private int extractedVectors = 0;
        /*
        private void PollInternal()
        {
            Receiver receiver = null;
            Sensor sensor = null;
            Decoder decoder = null;
            int id = 0;
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                sensor = this.wocketsController._Sensors[i];
                receiver = this.wocketsController._Receivers[sensor._Receiver];
                decoder = sensor._Decoder;
                id = i;
                if ((receiver._Running == true) && (receiver._Type == ReceiverTypes.HTCDiamond))
                    break;                
            }
            while (true)
            {
                try
                {
                    int numDecodedPackets = 0;
                    int dataLength = receiver.Read();
                    if (dataLength > 0)
                    {
                        numDecodedPackets = decoder.Decode(sensor._ID, receiver._Buffer, dataLength);
                        this.disconnected[sensor._ID] = 0;
                        this.AccumPackets[id] += numDecodedPackets;
                    }
                    this.AccumPackets[id + 6] += numDecodedPackets;
                }
                catch (Exception e)
                {
                    Logger.Warn("Internal " + sensor._ID + " has disconnected " + e.Message);
                    receiver.Initialize();
                    receiver._Running = true;
                }

                Thread.Sleep(30);
            }
        }*/

   

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
                    //GraphAccelerometerValues();                
                Thread.Sleep(50);
            }
        }
        /*
        private void SaveWockets()
        {
            while (true)
            {
                try
                {
                    for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
                    {
                        this.wocketsController._Sensors[i].Save();
                        Thread.Sleep(50);
                    }
                }
                catch (Exception ee)
                {
                    Logger.Error(ee);
                }
                
            }
        }
         */
        private void readDataTimer_Tick(object sender, EventArgs e)
        {
            
            int zeroes = 0;
            for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
            {
                if (this.wocketsController._Receivers[i].Disconnected != 0)
                {
                    this.wocketsController._Receivers[i].Disconnected += 1;
                    if (this.wocketsController._Receivers[i].Disconnected >= 3600 && !this.play_sound)
                    {
                        this.play_sound = true;
                        alert.LoopPlay();
                    }
                }
                else
                {
                    zeroes += 1;
                }
            }

            if (zeroes == 6 && this.play_sound)
            {
                alert.Play();
                this.play_sound = false;
            }

            this.SRcounter++;
           /* if (this.SRcounter == 800)
            {
                foreach (Sensor s in this.wocketsController._Sensors)
                {
                    Wockets.Sensors.Accelerometers.Wocket w = (Wockets.Sensors.Accelerometers.Wocket)s;
                    w._Config_Timer = 255;
                    //rf.Send(Wockets.Data.Commands.RFCOMMCommand.SetCAL(1,2,3,4,5,6));
                }
            }*/
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

                foreach (Receiver r in this.wocketsController._Receivers)
                {
                    RFCOMMReceiver rf = (RFCOMMReceiver)r;
                    rf.Send(Wockets.Data.Commands.RFCOMMCommand.GetBT());
                    //rf.Send(Wockets.Data.Commands.RFCOMMCommand.SetCAL(3, 5, 6, 8, 9, 11));
                  //  rf.Send(Wockets.Data.Commands.RFCOMMCommand.GetCAL());
                }
                updateCommand("Sent Battery Request");
            }
            
            if (isQuitting)
            {
                this.wocketsController.Dispose();

                this.alert.Stop();

                if (trainingTW != null)
                {
                    trainingTW.Flush();
                    trainingTW.Close();
                    trainingTW = null;
                }
                if (structureTW != null)
                {
                    structureTW.Flush();
                    structureTW.Close();
                    structureTW = null;
                }

                Logger.Close();
                FeatureExtractor.Cleanup();
                

#if (PocketPC)

                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();

#else
                Environment.Exit(0);
#endif
            }

            /* 
         * 
         for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
         {
             String key="W" + this.wocketsController._Sensors[i]._ID;
             ((PictureBox)this.sensorStatus[key]).Image = (Image)this.sensorStat[key];

         }

        
         if ((this.tabControl1.SelectedIndex == 0) && (isPlotting))
         {
             GraphAccelerometerValues();
         }
         */
            /*

            #region Classifying activities

#if (PocketPC)
            if (isClassifying == true)
            {
                double lastTimeStamp = FeatureExtractor.StoreWocketsWindow();//WocketsTimer.LastTimeStamp;//WocketsTimer.FeatureExtractor.StoreMITesWindow();
                if (FeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                {
                    Instance newinstance = new Instance(instances.numAttributes());
                    newinstance.Dataset = instances;
                    for (int i = 0; (i < FeatureExtractor.Features.Length); i++)
                        newinstance.setValue(instances.attribute(i), FeatureExtractor.Features[i]);
                    double predicted = classifier.classifyInstance(newinstance);
                    string predicted_activity = newinstance.dataset().classAttribute().value_Renamed((int)predicted);

                    int currentIndex = (int)labelIndex[predicted_activity];
                    labelCounters[currentIndex] = (int)labelCounters[currentIndex] + 1;
                    classificationCounter++;

                    if (classificationCounter == this.classifierConfiguration._SmoothWindows)
                    {
                        classificationCounter = 0;
                        int mostCount = 0;
                        string mostActivity = "";
                        Color indicate;
                        int level;
                        for (int j = 0; (j < labelCounters.Length); j++)
                        {
                            level=240-240*labelCounters[j]/this.classifierConfiguration._SmoothWindows;
                            indicate = Color.FromArgb(level, level, level);
                            this.ActGUIlabels[j].ForeColor = indicate;
                            this.ActGUIlabels[j].Invalidate();
                            if (labelCounters[j] > mostCount)
                            {
                                mostActivity = activityLabels[j];
                                mostCount = labelCounters[j];
                            }
                            labelCounters[j] = 0;
                        }

    
                        pieChart.SetActivity(mostActivity);
                        if (this.aList.getEmptyPercent() == 1)
                            this.aList.reset();
                        else
                            this.aList.increment(mostActivity);

                        if (previousActivity != mostActivity)
                        {
                            this.activityTimer.stop();
                            this.activityTimer.reset();
                            currentCalories = 0;
                        }
                        else
                        {
                            if (this.activityTimer.isRunning() == false)
                                this.activityTimer.start();
                        }

                        if (mostActivity == "standing")
                        {
                            currentCalories += 1;
                            totalCalories += 1;
                        }
                        else if (mostActivity == "walking")
                        {
                            currentCalories += 2;
                            totalCalories += 2;
                        }
                        else if (mostActivity == "brisk-walking")
                        {
                            currentCalories += 4;
                            totalCalories += 4;
                        }
                        else
                        {
                            currentCalories += 1;
                            totalCalories += 1;
                        }
                   
                        pieChart.SetCalories(totalCalories, currentCalories);
                        pieChart.Data = this.aList.toPercentHashtable();
                        pieChart.Invalidate();
                        previousActivity = mostActivity;
                        
                    }
                }
            }

#endif


            #endregion Classifying activities

            #region Training

            if (isTraining)
            {
                //create arff file
                if (trainingTW == null)
                {
                    string arffFileName = this.storageDirectory+ "\\output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";                   
                    trainingTW = new StreamWriter(arffFileName);                    
                    trainingTW.WriteLine("@RELATION wockets");
                    string arffHeader = FeatureExtractor.GetArffHeader();
                    arffHeader += "\n@ATTRIBUTE activity {";
                    int i = 0;
                    for (i = 0; (i < ((this.annotatedSession.OverlappingActivityLists[0]).Count - 1)); i++)
                        arffHeader+=this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + ",";
                    arffHeader+=this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + "}\n";
                    arffHeader+="\n@DATA\n\n";
                    
                    
                    
                    trainingTW.WriteLine(arffHeader);
                    string structureArffFile = this.storageDirectory + "\\structure.arff";
                    structureTW = new StreamWriter(structureArffFile);
                    structureTW.WriteLine("@RELATION wockets");
                    structureTW.WriteLine(arffHeader);

                }
                string current_activity = "unknown";
                if (this.currentRecord != null)
                {
                    double lastTimeStamp = FeatureExtractor.StoreWocketsWindow();
                    if (FeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                    {
                        current_activity = this.currentRecord.Activities._CurrentActivity;
                        string arffSample = FeatureExtractor.toString() + "," + current_activity;
                        trainingTW.WriteLine(arffSample);
                        extractedVectors++;
                        if (structureFileExamples < 10)
                        {
                            structureTW.WriteLine(arffSample);
                            structureFileExamples++;
                        }
                    }
                }
            }
            else
            {
                if (trainingTW != null)
                {
                    structureTW.Flush();
                    structureTW.Close();                  
                    structureTW = null;
                    trainingTW.Flush();
                    trainingTW.Close();
                    trainingTW = null;
                }
            }
            #endregion Training
            #region CollectingData


           
            #endregion CollectingData

            
            #region Store the sensor data

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)            
                this.wocketsController._Sensors[i].Save();            
            #endregion Store the sensor data
*/
            

  

        }
        private void updateCommand(string s)
        {
            this.CommandBox.Text += s+"\r\n";
            this.CommandBox.SelectionStart = this.CommandBox.Text.Length;
            this.CommandBox.ScrollToCaret();
        }


        private int CurrentPanel
        {
            set
            {
                if (value != this.panelSwitch)
                {
                    this.panelArray[this.panelSwitch].Visible = false;
                    this.panelSwitch = value;
                    this.panelArray[this.panelSwitch].Visible = true;
                }
            }

            get
            {
                return this.panelSwitch;
            }
        }

        delegate void UpdateGraphCallback();
        public void UpdateGraph()
        {
            // InvokeRequired required compares the thread ID of the
            // calling thread to the thread ID of the creating thread.
            // If these threads are different, it returns true.
            if (this.panel1.InvokeRequired)
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
            if (this.panel1.InvokeRequired)
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