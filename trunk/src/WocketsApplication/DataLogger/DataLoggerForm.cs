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

using WocketsApplication.Feedback;

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
        /// <summary>
        /// True if the progress thread should quit
        /// </summary>
        private bool progressThreadQuit = false;
        /// <summary>
        /// Counter to update the number of samples
        /// </summary>
        private int printSamplingCount = 0;
        /// <summary>
        /// An array list of the different buttons of the annotator
        /// </summary>
        private ArrayList categoryButtons;
        /// <summary>
        /// An array list that stores the current index for each button
        /// </summary>
        private ArrayList buttonIndex;
        /// <summary>
        /// A variable that stores the longest label on a category button for dynamic resizing of the buttons
        /// </summary>
        private string longest_label = "";

        #endregion Definition of GUI Components

        #region Sampling Rate Components
        /// <summary>
        /// An array for accumulating received packets to calculate sample rate.
        /// </summary>
        private int[] AccumPackets;
        /// <summary>
        /// Last time of rate calculation
        /// </summary>
        private long LastTime;
        /// <summary>
        /// Counter to determine when to take datetime
        /// </summary>
        private int SRcounter=0;
        /// <summary>
        /// Change in time since last calculation
        /// </summary>
        private long deltaT;
        #endregion Sampling Rate Components

        #region Definition of Logging Variables and Flags
        /// <summary>
        /// A constant that specifies how often to flush logging data
        /// </summary>
        private const int FLUSH_TIMER_MAX = 6000;
        /// <summary>
        /// Counter used to log status data when it reaches its max
        /// </summary>
        int flushTimer = 0;

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
        private PLFormatLogger aPLFormatLogger;
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
        /// Stores the arff file name where the extracted features will be stored
        /// </summary>
        private string arffFileName;
        /// <summary>
        /// Arff file Text writer
        /// </summary>
        private TextWriter tw;

        /// <summary>
        /// The time when training an activity started
        /// </summary>
        int startActivityTime;
        /// <summary>
        /// A counter for windows used in smoothening
        /// </summary>
        private int classificationCounter;
        /// <summary>
        /// Stores counters for each label to be used during smoothening
        /// </summary>
        private int[] labelCounters;

        #endregion Definition of classification variables

        #region Definition of different software modes


        /// <summary>
        /// True if the software is required to do real-time classification otherwise false
        /// </summary>
        private bool isClassifying;

        private int vibrateTimer = 0;
        private Vibrator vibrator = null;
        private bool vibrateStatus = false;

        #endregion Definition of different software modes


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
            if (mode == 1)
                InitializeAnnotator(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 2)
                InitializeDataLogger(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            else if (mode == 3)
                InitializeActivityTracker(storageDirectory, wocketsController, annotatedSession, classifierConfiguration);
            this.AccumPackets = new int[wocketsController._Receivers.Count];
            this.LastTime = DateTime.Now.Ticks;


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

     


            //Initialize the timers

            InitializeTimers();

            //Initialize different GUI components
            InitializeInterface();


#if (PocketPC)
            this.tabControl1.TabPages.RemoveAt(4);
            this.tabControl1.TabPages.RemoveAt(3);
            this.tabControl1.TabPages.RemoveAt(2);
            this.tabControl1.TabPages.RemoveAt(0);
            this.tabControl1.SelectedIndex = 0;
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
            this.vibrator = new Vibrator();
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

            #region Bluetooth reception channels initialization
            //Initialize and search for wockets connections
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Initializing receivers ... searching " + this.wocketsController._Receivers.Count + " BT receivers\r\n";

            //Try to initialize all receivers 10 times then exit
            int initializationAttempt = 0;
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

            this.tabControl1.TabPages.RemoveAt(4);
            this.tabControl1.SelectedIndex = 0;
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
            InitializeLogging(this.storageDirectory);
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
                    currentReceiver = this.wocketsController._Receivers[sensor._Receiver];
                    if (currentReceiver._Running == true)
                        currentReceiver.Read();
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

        #endregion Collect Data Constructor (Wockets, MITes, Builtin)

        #region Classifier constructor

        public void InitializeActivityTracker(string storageDirectory, WocketsController wocketsController, Session annotatedSession, DTConfiguration classifierConfiguration)
        {
            this.vibrator = new Vibrator();
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
#if (PocketPC)

            this.tabControl1.TabPages.RemoveAt(4);
            this.tabControl1.SelectedIndex = 0;
#else
            this.ShowForms();
#endif


            #endregion Initialize GUI Components
            isClassifying = true;


            #region Initialize Feature Extraction

            FeatureExtractor.Initialize(this.wocketsController, this.classifierConfiguration, this.annotatedSession.OverlappingActivityLists[0]);//this.masterDecoder, dataDirectory, this.annotation, this.sensors, this.configuration);
            #endregion Initialize Feature Extraction

            labelIndex = new Hashtable();
            instances = new Instances(new StreamReader(this.storageDirectory + "\\realtime-output.arff"));
            instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
            classifier = new J48();
            /* if (!File.Exists(this.storageDirectory+"\\model.xml"))
             {
                 classifier.buildClassifier(instances);
                 TextWriter tc = new StreamWriter("model.xml");
                 classifier.toXML(tc);
                 tc.Flush();
                 tc.Close();
             }
             else*/
            classifier.buildClassifier(this.storageDirectory + "\\model.xml", instances);


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


            weka.core.Attribute ClassAttribute = new weka.core.Attribute("activity", fvClassVal);

            isClassifying = true;

            #region Initialize Quality Tracking variables
            //InitializeQuality();
            #endregion Initialize Quality Tracking variables

            #region Initialize Logging
            InitializeLogging(this.storageDirectory);
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
                    currentReceiver = this.wocketsController._Receivers[sensor._Receiver];
                    if (currentReceiver._Running == true)
                        currentReceiver.Read();
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
                    //this.mitesDecoders[receiver.ID] = new MITesDecoder();
                    //receiver.Status = SXML.Receiver.STATUS_CONNECTED;
                    /*
                    if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                    {
                        byte[] cmd = new byte[8];
                        cmd[0] = (byte)36;
                        cmd[1] = (byte)36;
                        cmd[2] = (byte)36;
                        //SW,0640 1 sec
                                                   
                        this.wocketsController._Receivers[i].Write(cmd,3);
                        Thread.Sleep(1000);
                        cmd[0] = (byte)'S';
                        cmd[1] = (byte)'W';
                        cmd[2] = (byte)',';
                        cmd[3] = (byte)'0';
                        cmd[4] = (byte)'0';
                        cmd[5] = (byte)'0';
                        cmd[6] = (byte)'0';
                        cmd[7] = (byte)13;
                        this.wocketsController._Receivers[i].Write(cmd, 8);
                        Thread.Sleep(1000);
                        cmd[0] = (byte)'S';
                        cmd[1] = (byte)'Y';
                        cmd[2] = (byte)',';
                        cmd[3] = (byte)'0';
                        cmd[4] = (byte)'0';
                        cmd[5] = (byte)'0';
                        cmd[6] = (byte)'4';
                        cmd[7] = (byte)13;
                        this.wocketsController._Receivers[i].Write(cmd, 8);
                        Thread.Sleep(1000);
                        cmd[0] = (byte)'-';
                        cmd[1] = (byte)'-';
                        cmd[2] = (byte)'-';
                        cmd[3] = (byte)13;
                        this.wocketsController._Receivers[i].Write(cmd, 4);
                        this.wocketsController._Receivers[i].Read();
                        if ((this.wocketsController._Receivers[i]._Buffer[0] == 'E') &&
                            (this.wocketsController._Receivers[i]._Buffer[1] == 'N') &&
                            (this.wocketsController._Receivers[i]._Buffer[2] == 'D'))
                        {
                            cmd[0] = (byte)'-';
                            cmd[1] = (byte)'-';
                            cmd[2] = (byte)'-';

                            //this.wocketsController._Receivers[i].Write(cmd, 4);
                            //this.wocketsController._Receivers[i].Read();
                        }
                    }
                     */
                    this.wocketsController._Receivers[i]._Running = true;
                }

            }

            return true;
        }

#endif





        //Initialize objects for logging and storing wockets and MITes data
        private void InitializeLogging(string dataDirectory)
        {

            aPLFormatLogger = new PLFormatLogger(this.wocketsController,
                                                         dataDirectory + "\\data\\raw\\PLFormat\\");
        }
    
        #endregion Initialization Methods



        public bool AutoTraining
        {
            get
            {
                return this.menuItem7Tab2.Checked;
            }
        }

        public bool IsTraining
        {
            get
            {
                return this.menuItem5Tab2.Checked;
            }
        }




        #region Resize Event Handlers

        private void OnResize(object sender, EventArgs ee)
        {

            if ((this.Width > Constants.FORM_MIN_WIDTH) && (this.Height > Constants.FORM_MIN_HEIGHT))
            {

                this.tabControl1.Width = this.ClientSize.Width;
                this.tabControl1.Height = this.ClientSize.Height;
                this.tabPage1.Width = this.panel1.Width = this.tabPage2.Width = this.tabPage3.Width = this.tabPage4.Width = this.tabControl1.ClientSize.Width;
                this.tabPage1.Height = this.panel1.Height = this.tabPage2.Height = this.tabPage3.Height = this.tabPage4.Height = this.tabControl1.ClientSize.Height;


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
                int button_width = this.tabPage2.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
                int button_height = (this.tabPage2.ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - (this.annotatedSession.OverlappingActivityLists.Count * Constants.WIDGET_SPACING)) / (this.annotatedSession.OverlappingActivityLists.Count + 1);
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
                this.startStopButton.Size = new System.Drawing.Size(button_width, button_height);
                this.resetButton.Size = new System.Drawing.Size(button_width, button_height);
                this.startStopButton.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, button_y + button_id * delta_y);
                this.resetButton.Location = new System.Drawing.Point(this.startStopButton.Location.X + this.startStopButton.Size.Width + Constants.WIDGET_SPACING, button_y + button_id * delta_y);
                this.startStopButton.Font = buttonFont;
                this.resetButton.Font = buttonFont;

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



        private void startStopButton_Click(object sender, EventArgs e)
        {
            Button button = (Button)sender;
            //button state is now start
            if (button.BackColor == System.Drawing.Color.Green)
            {
                // this.startSound.Play();
                //Generator generator = new Generator();
                //generator.InitializeSound(this.Handle.ToInt32());
                //generator.CreateBuffer();

                this.startStopButton.Text = "Stop";
                this.startStopButton.BackColor = System.Drawing.Color.Red;
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
                foreach (Button category_button in categoryButtons)
                {
                    int button_id = Convert.ToInt32(category_button.Name);
                    ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                    string current_label = category[(int)this.buttonIndex[button_id]]._Name;
                    this.currentRecord.Activities.Add(new Activity(current_label, category._Name));
                    category_button.Enabled = false;
                }

            }

            else if (button.BackColor == System.Drawing.Color.Red)
            {
                // this.stopSound.Play();
                this.startStopButton.Text = "Start";
                this.startStopButton.BackColor = System.Drawing.Color.Green;
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

                //each time an activity is stopped, rewrite the file on disk, need to backup file to avoid corruption
                //this.annotation.ToXMLFile();
                //this.annotation.ToCSVFile();
                TextWriter tw = new StreamWriter(this.storageDirectory + "\\AnnotationIntervals.xml");
                // write a line of text to the file
                tw.WriteLine(this.annotatedSession.ToXML());
                // close the stream
                tw.Close();

                foreach (Button category_button in categoryButtons)
                    category_button.Enabled = true;

            }
        }

        private void resetButton_Click(object sender, EventArgs e)
        {
            //this.resetSound.Play();
            this.startStopButton.Text = "Start";
            this.startStopButton.BackColor = System.Drawing.Color.Green;
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

        private void menuItem21_Click(object sender, EventArgs e)
        {
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
            tw.Close();
            this.menuItem6Tab2.Enabled = false;
            this.menuItem5Tab2.Checked = false;
            this.menuItem5Tab2.Enabled = true;
            this.trainingLabel.Visible = false;

            if (this.annotatedSession.OverlappingActivityLists.Count == 1) //if 1 category
            {
                //enable whatever was not chosen to allow the user to switch the training mode
                if (this.menuItem8Tab2.Checked)
                    this.menuItem7Tab2.Enabled = true;
                else
                    this.menuItem8Tab2.Enabled = true;
            }
            this.startStopButton.Enabled = false;
            this.resetButton.Enabled = false;
            ((Button)this.categoryButtons[0]).Visible = true;
            ((Button)this.categoryButtons[0]).Enabled = true;
        }

        public void SetText(string label, int control_id)
        {
            // InvokeRequired required compares the thread ID of the
            // calling thread to the thread ID of the creating thread.
            // If these threads are different, it returns true.
            if (this.label1.InvokeRequired)
            {
                SetTextCallback d = new SetTextCallback(SetText);
                this.Invoke(d, new object[] { label, control_id });
            }
            else
            {
                if (control_id == GOOD_TIMER)
                    this.label1.Text = label;
                else if (control_id == OVERALL_TIMER)
                {
                    this.label3.Text = label;

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
                if (isGood)
                {
                    if (this.startStopButton.BackColor == System.Drawing.Color.Red)
                        this.goodTimer.start();
                }
                else
                {
                    if (this.startStopButton.BackColor == System.Drawing.Color.Red)
                        this.goodTimer.stop();
                }
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


#if (PocketPC)
        void tabControl1_Changed(object sender, EventArgs e)
        {
            if (this.tabControl1.SelectedIndex == 1)
                this.Menu = this.mainMenuTab2;
            else if (this.tabControl1.SelectedIndex == 0)
                this.Menu = this.mainMenu1;
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
            if (this.tabControl1.TabIndex == 0)
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

        private bool isCollectingData = false;


       // private TextWriter ttw = null;
        //double prevTS = 0;

        private Thread plottingThread = null;
        private void readDataTimer_Tick(object sender, EventArgs e)
        {

            if (isQuitting)
            {
                for (int i = 0; (i < this.wocketsController._Receivers.Count); i++)
                {

                    if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                    {
                        Thread.Sleep(100);
                        //this.bluetoothControllers[i].cleanup();
                        this.wocketsController._Receivers[i].Dispose();
                        Thread.Sleep(1000);
                    }

                    Thread.Sleep(100);
                }


                

                if (aPLFormatLogger != null)
                {
                    aPLFormatLogger.FlushBytes();
                    aPLFormatLogger.ShutdownFiles();
                }
                FeatureExtractor.Cleanup();

               // ttw.Flush();
               // ttw.Close();
#if (PocketPC)

                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();

#else
                Environment.Exit(0);
#endif
            }
            #region Bluetooth Reconnection Code
#if (PocketPC)

            for (int i = 0; (i < this.wocketsController._Receivers.Count); i++)
            {
                if (this.wocketsController._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                {
                    if ((this.bluetoothConnectors[this.wocketsController._Receivers[i]._ID]!=null) &&
                        (!this.bluetoothConnectors[this.wocketsController._Receivers[i]._ID].Reconnecting) &&
                        (this.wocketsController._Receivers[i]._Running == false))
                        this.bluetoothConnectors[this.wocketsController._Receivers[i]._ID].Reconnect();
                    
                }

            }


#endif

            #endregion Bluetooth Reconnection Code

            #region Poll All Wockets and MITes and Decode Data

            Receiver currentReceiver = null;
            Sensor sensor=null;
            try
            {
                for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
                {
                    sensor = this.wocketsController._Sensors[i];
                    currentReceiver = this.wocketsController._Receivers[sensor._Receiver];
                    if (currentReceiver._Running == true)
                    {
                        Decoder decoder = this.wocketsController._Decoders[sensor._Decoder];
                        int dataLength = currentReceiver.Read();
                        int numDecodedPackets = 0;
                        if (dataLength > 0)
                        {                 
                            numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, dataLength);
                        }

                        #region


                        /*
                        #region Plot Decoded Data Only
                        if ((this.tabControl1.SelectedIndex == 0) && (isPlotting))
                        {
                            aWocketsPlotter.PlotFrom[i] = decoder._Size-numDecodedPackets;
                            GraphAccelerometerValues();
                        }
                        #endregion Plot Decoded Data Only

                        */

                        //clear processed timestamps
                        /*
                        if (currentReceiver._Type == ReceiverTypes.RFCOMM)
                        {
                            int numBatches = ((RFCOMMReceiver)currentReceiver).BatchBytes.Count;
                            double t1 = (double)((RFCOMMReceiver)currentReceiver).BatchTimestamps[0];
                            double t2 = (double)((RFCOMMReceiver)currentReceiver).BatchTimestamps[numBatches - 1];

                            //If batches exceed 3 seconds
                            if (t2 - t1 > 3000)
                            {

                                //Find the last batch for the decoded data and use its
                                //timestamp as the last timestamp t2
                                int sumBytes = numDecodedPackets * WocketsAccelerationData.NUM_RAW_BYTES;
                                int lastBatch = -1;
                                for (int j = 0; (j < numBatches); j++)
                                {
                                    sumBytes -= (int)((RFCOMMReceiver)currentReceiver).BatchBytes[j];
                                    if (sumBytes <= 0)
                                    {

                                        t2 = (double)((RFCOMMReceiver)currentReceiver).BatchTimestamps[j];
                                        //the decoded packets end at the end of a batch
                                        if (sumBytes == 0)
                                            lastBatch = j;
                                        else //decoded packets are at the middle of a batch
                                            lastBatch = j - 1;
                                        break;
                                    }
                                }

                                //Remove timestamp batches that have been completely decoded
                                if (lastBatch >= 0)
                                {
                                    ((RFCOMMReceiver)currentReceiver).BatchBytes.RemoveRange(0, lastBatch + 1);
                                    ((RFCOMMReceiver)currentReceiver).BatchTimestamps.RemoveRange(0, lastBatch + 1);

                                    //Reset decoder
                                    decoder._Size = 0;
                                }

                            }
                        }*/
                        #endregion
                        #region Calculate Sampling Rate
                        this.SRcounter += 1;
                        this.AccumPackets[sensor._ID] += numDecodedPackets;
                        if (this.SRcounter >= 100)
                        {
                            this.deltaT=Math.Abs(DateTime.Now.Ticks - this.LastTime);
                            if (this.deltaT >= 50000000)
                            {
                                for (int x=0; x < this.wocketsController._Sensors.Count; x++)
                                {
                                    String labelKey = "W" + this.wocketsController._Sensors[x]._ID;
                                    this.wocketsController._Sensors[x].setSR(this.AccumPackets[this.wocketsController._Sensors[x]._ID] /5);
                                    Label t = (System.Windows.Forms.Label)this.sensorLabels[labelKey];
                                    t.Text="W" + this.wocketsController._Sensors[x]._ID + ": " + this.wocketsController._Sensors[x].getSR() + "/90";
                                }
                                this.SRcounter = 0;
                                this.LastTime = DateTime.Now.Ticks;
                                for (int x=0; x < this.AccumPackets.Length; x++)
                                {
                                    this.AccumPackets[x] = 0;
                                }
                                
                            }
                        }


                        #endregion Calculate Sampling Rate

                        ((PictureBox)this.sensorStatus["W" + this.wocketsController._Sensors[i]._ID]).Image = connectedWocketImage;
                       
                    }
                }

            }
            //Thrown when there is a Bluetooth failure                    
            //TODO: Make sure no USB failure happening
            catch (Exception ex)
            {

                
                ((PictureBox)this.sensorStatus["W" + sensor._ID]).Image=disconnectedWocketImage;                
                this.bluetoothConnectors[currentReceiver._ID] = new BluetoothConnector(currentReceiver, this.wocketsController);                
                currentReceiver._Running = false;
                return;
            }



            #endregion Poll All Wockets and MITes and Decode Data

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
                        for (int j = 0; (j < labelCounters.Length); j++)
                        {
                            if (labelCounters[j] > mostCount)
                            {
                                mostActivity = activityLabels[j];
                                mostCount = labelCounters[j];
                            }
                            labelCounters[j] = 0;
                        }

                        if ((mostActivity == "Flapping") || (mostActivity == "flapping"))
                        {

                            vibrator.StartVibrate();
                            vibrateTimer = -1;
                        }
                        else if ((mostActivity == "Rocking") || (mostActivity == "rocking"))
                        {

                            vibrator.StartVibrate();
                            vibrateTimer = -1;
                        }
                        else if ((mostActivity == "Flaprock") || (mostActivity == "flaprock"))
                        {

                            vibrator.StartVibrate();
                            vibrateTimer = -1;
                        }
                        else
                            vibrator.StopVibrate();

                        if (vibrateStatus != vibrator.isVibrateON)
                        {
                            vibrateStatus = vibrator.isVibrateON;
                            TextWriter vbtw = new StreamWriter(this.storageDirectory + "\\vibrate.csv", true);
                            vbtw.Write(DateTime.Now.ToLongTimeString() + ",");
                            if (vibrateStatus)
                                vbtw.WriteLine("vibrate");
                            else
                                vbtw.WriteLine("stopvibrate");
                            vbtw.Close();
                        }

                        if (vibrateTimer > 500) //5 seconds
                            vibrateTimer = -1;
                        vibrateTimer++;

                        /*pieChart.SetActivity(mostActivity);
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
                        */
                    }
                }
            }

#endif


            #endregion Classifying activities

            #region CollectingData

/*
            if (ttw == null)
                ttw = new StreamWriter("seqs.csv");
            isCollectingData = true;
            if (isCollectingData)
            {

                //store sum of abs values of consecutive accelerometer readings                
                for (int i = 0; (i < this.wocketsController._Decoders.Count); i++)
                    for (int j = 0; (j < this.wocketsController._Decoders[i]._Size); j++)
                    {

                        if (this.wocketsController._Decoders[i]._Data[j].Type == SensorDataType.ACCEL)
                        {
                            int channel = 0, x = 0, y = 0, z = 0;
                           // channel = (int)this.wocketsController._Decoders[i]._Data[j].Channel;
                            x = (int)((AccelerationData)this.wocketsController._Decoders[i]._Data[j]).X;
                            y = (int)((AccelerationData)this.wocketsController._Decoders[i]._Data[j]).Y;
                            z = (int)((AccelerationData)this.wocketsController._Decoders[i]._Data[j]).Z;

                            int msec=(y<<8)|z;
                            ttw.WriteLine(x + "," + msec);
                        }
                    }
            }
             */
            #endregion CollectingData

            
            #region Store the sensor data
#if (PocketPC)
            aPLFormatLogger.Save();
#endif
            if (flushTimer == 0)
                aPLFormatLogger.FlushBytes();
            if (flushTimer > FLUSH_TIMER_MAX)
                flushTimer = -1;
            flushTimer++;
           
            #endregion Store the sensor data

            

            if ((this.tabControl1.SelectedIndex == 0) && (isPlotting))
            {
                GraphAccelerometerValues();
            }

            //Reset all decoders

            for (int i = 0; (i < this.wocketsController._Decoders.Count); i++)
              this.wocketsController._Decoders[i]._Size = 0;
        }


        #endregion Timer Methods
    }
}