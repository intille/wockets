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

#if (PocketPC)
using WocketsApplication.Feedback;
#endif

namespace WocketsApplication.Calibrator
{
    public partial class CalibratorForm : Form
    {
        #region Declarations of Objects

        #region Definition of Plotting and Graphing Variables
        /// <summary>
        /// Set when the form is resized
        /// </summary>
        private bool isResized = false;
        /// <summary>
        /// True when form plots otherwise false
        /// </summary>
        private bool isPlotting = true;
        /// <summary>
        /// Backbuffer for plotting the accelerometer data
        /// </summary>
        private Bitmap backBuffer = null;
        //TODO: change the name of the plotter to something reasonable since it is generic
        /// <summary>
        /// A plotter for accelerometer data
        /// </summary>
        private WocketsScalablePlotter aWocketsPlotter;

        private Pen aPen = new Pen(Color.Wheat);
        private SolidBrush aBrush = new SolidBrush(Color.White);
        private SolidBrush blueBrush = new SolidBrush(Color.LightBlue);
        private SolidBrush redBrush = new SolidBrush(Color.Red);

        #endregion Definition of Plotting and Graphing Variables


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

        private Thread aPlottingThread = null;

        #endregion Definition of GUI Components



        #region Wockets and MITes Variables



        #region Definition of controllers for different reception channels
        //TODO: Define a single interface for ReceiverController and extend it to use USB,Bluetooth or DiamondTouch
        //  private MITesReceiverController[] mitesControllers;

        //private BluetoothController[] bluetoothControllers;
        private BluetoothConnector[] bluetoothConnectors;

        #endregion Definition of controllers for different reception channels



        #region Definition of built-in sensors polling threads   (Pocket PC Only)
#if (PocketPC)
        /// <summary>
        /// Counter for the next polling time for the built-in accelerometer
        /// </summary>
        private int pollingTime = Environment.TickCount;
        /// <summary>
        /// A polling thread for the built-in accelerometer
        /// </summary>

#endif
        #endregion Definition of built-in sensors polling threads   (Pocket PC Only)

        #endregion Wockets and MITes Variables

     


#if (PocketPC)
        [DllImport("coredll.dll")]
        public static extern int PlaySound(
            string szSound,
            IntPtr hModule,
            int flags);
#endif

        #endregion Declarations of Objects
        private Image[] calibrationImages;

        private const int CALIBRATION_SAMPLES = 1200;
        private int[][] samples;
        private double time=0;
        private int currentIndex = -1;

        private int sampleCounter = 0;
        private int numOfSamples = 0;
        private DateTime startTime;
        private DateTime endTime;
        private bool isTracking = false;

        private Thread aPollingThread = null;


        public CalibratorForm(string storageDirectory, WocketsController wocketsController)
        {


            this.calibrationImages = new Image[7];


            for (int i = 0; (i < 7); i++)
                this.calibrationImages[i] = (Image)new Bitmap(Constants.CALIBRATIONS_DIRECTORY + "calibration" + (i + 1) + ".gif");


            Logger.InitLogger(storageDirectory);
            this.storageDirectory = storageDirectory;
            this.wocketsController = wocketsController;





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



            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Completed\r\n";

            //Remove classifier tabs


            #endregion Initialize GUI Components


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


        private WocketsController wocketsController;
        private string storageDirectory;



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



        #endregion Collect Data Constructor (Wockets, MITes, Builtin)

        #region Initialization Methods






        //Initialize Bluetooth receiver channels includes wockets, sparkfun, Bluetooth enabled MITes
        private bool InitializeBluetoothReceivers()
        {
            //Initialize all defined reception channels Bluetooth
            //foreach (Receiver receiver in this.sensors.Receivers)
            for (int i = 0; (i < this.wocketsController._Receivers.Count); i++)
            {
                //If reception channel is of type Bluetooth and is not already initialized
                if ((this.wocketsController._Receivers[i]._Type == ReceiverTypes.RFCOMM) && (this.wocketsController._Receivers[i]._Running == false))
                {
                    //Create a Bluetooth controller
                    while (progressMessage != null) Thread.Sleep(50);
                    progressMessage = "Initializing Bluetooth for " + ((RFCOMMReceiver)this.wocketsController._Receivers[i])._Address + " ...\r\n";
                    //this.bluetoothControllers[this.wocketsController._Receivers[i]._ID] = new BluetoothController();
                    try
                    {
                        //this.bluetoothControllers[this.wocketsController._Receivers[i]._ID].initialize(((RFCOMMReceiver)this.wocketsController._Receivers[i])._AddressBytes, ((RFCOMMReceiver)this.wocketsController._Receivers[i])._PIN);
                        this.wocketsController._Receivers[i].Initialize();
                    }
                    catch (Exception e)
                    {
                        while (progressMessage != null) Thread.Sleep(50);
                        progressMessage = "Failed to find" + ((RFCOMMReceiver)this.wocketsController._Receivers[i])._Address + " ...\r\n";
                        return false;
                    }
                    
                    this.wocketsController._Receivers[i]._Running = true;
                }

            }

            return true;
        }





        #endregion Initialization Methods








        #region Resize Event Handlers
#if (PocketPC)
        private void OnResize(object sender, EventArgs ee)
        {

            if ((this.Width > Constants.FORM_MIN_WIDTH) && (this.Height > Constants.FORM_MIN_HEIGHT))
            {

                this.tabControl1.Width = this.ClientSize.Width;
                this.tabControl1.Height = this.ClientSize.Height;
                this.tabPage1.Width = this.panel1.Width =  this.tabControl1.ClientSize.Width;
                this.tabPage1.Height = this.panel1.Height =  this.tabControl1.ClientSize.Height;


                //Intialize Labels 40% of the screen

                int num_rows = (int)((this.wocketsController._Sensors.Count + 3) / 2); //additional row for HR and total sampling rate
                int textBoxHeight = ((int)(0.40 * this.tabPage1.ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
                int textBoxWidth = ((this.tabPage1.ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 2);
                int currentTextY = (int)(this.tabPage1.Height * 0.60);
                int leftTextX = Constants.WIDGET_SPACING;
                int rightTextX = (Constants.WIDGET_SPACING * 2) + textBoxWidth;
                int currentTextX = Constants.WIDGET_SPACING;

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
                    labelKey = "Wocket" + this.wocketsController._Sensors[i]._ID;
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



                t = (System.Windows.Forms.Label)this.sensorLabels["calibration"];
                t.Font = textFont;
                t.Size = new System.Drawing.Size(textBoxWidth * 2, textBoxHeight/3);
                t.Location = new System.Drawing.Point(leftTextX, currentTextY + textBoxHeight + 5);
                if (currentTextX == leftTextX)
                    currentTextX = rightTextX;
                else
                {
                    currentTextX = leftTextX;
                    currentTextY += (textBoxHeight + Constants.WIDGET_SPACING);
                }

                this.button2.Font = textFont;
                this.button2.Width = textBoxWidth;
                this.button2.Height = textBoxHeight / 2;
                this.button2.Location = new Point((this.panel1.Width - this.button2.Width) / 2, t.Location.Y + t.Height +5);

                aWocketsPlotter = new WocketsScalablePlotter(this.panel1, this.wocketsController);
                
                this.isResized = true;
            }
        }
#else
        private void OnResizeForm3(object sender, EventArgs ee)
        {

        }


        private void OnResizeForm4(object sender, EventArgs ee)
        {


            if ((this.form4.Width > Constants.FORM_MIN_WIDTH) && (this.form4.Height > Constants.FORM_MIN_HEIGHT))
            {

                this.panel4.Width = this.form4.ClientSize.Width;
                this.panel4.Height = this.form4.ClientSize.Height;

                int counter = 0;
                int label_width = (this.panel4.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 3;
                int label_height = (this.panel4.ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - (this.wocketsController._Sensors.Count * Constants.WIDGET_SPACING)) / (this.wocketsController._Sensors.Count + 1);
                Form f = new Form();
                f.Width = label_width;
                f.Height = label_height;
                Font textFont = GUIHelper.CalculateBestFitFont(f.CreateGraphics(), Constants.MIN_FONT, Constants.MAX_FONT,
                     f.ClientSize, "E(Samp. Rate) ", new Font(Constants.FONT_FAMILY, (float)32.0, FontStyle.Bold), (float)0.9, (float)0.9);


                this.label7.Size = this.label8.Size = this.label9.Size = new Size(label_width, label_height);
                this.label7.Font = this.label8.Font = this.label9.Font = textFont;
                this.label7.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
                this.label8.Location = new System.Drawing.Point(Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
                this.label9.Location = new System.Drawing.Point(Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));

                counter++;
                //foreach (Sensor sensor in this.sensors.Sensors)
                                
                for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
                {

             

                    //setup the labels for the expected sampling rates
                    int sensor_id = this.wocketsController._Sensors[i]._ID;

                }
            }
        }

        private void OnResizeForm2(object sender, EventArgs ee)
        {
            if ((this.form2.Width > Constants.FORM_MIN_WIDTH) && (this.form2.Height > Constants.FORM_MIN_HEIGHT))
            {

                this.panel2.Width = this.form2.ClientSize.Width;
                this.panel2.Height = this.form2.ClientSize.Height;

                //Initialize Buttons
                int button_width = this.panel2.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
                int button_height = (this.panel2.ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - (this.annotatedSession.OverlappingActivityLists.Count * Constants.WIDGET_SPACING)) / (this.annotatedSession.OverlappingActivityLists.Count + 1);
                int button_x = Constants.WIDGET_SPACING;
                int button_y = Constants.WIDGET_SPACING * 2;

                int delta_y = button_height + Constants.WIDGET_SPACING;
                int button_id = 0;
                Form f = new Form();
                f.Size = new Size(button_width, button_height);
                Font buttonFont = GUIHelper.CalculateBestFitFont(f.CreateGraphics(), Constants.MIN_FONT, Constants.MAX_FONT,
                    f.ClientSize, longest_label, new Font(Constants.FONT_FAMILY, (float)32.0, FontStyle.Bold), (float)0.9, (float)0.9);
                foreach (System.Windows.Forms.Button button in categoryButtons)
                {
                    button.Location = new System.Drawing.Point(button_x, button_y + button_id * delta_y);
                    button.Font = buttonFont;
                    button.Size = new System.Drawing.Size(button_width, button_height);
                    button_id++;
                }

                //adjust round buttons start/stop -reset
                button_width = (this.panel2.Size.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 2;
                this.startStopButton.Size = new System.Drawing.Size(button_width, button_height);
                this.resetButton.Size = new System.Drawing.Size(button_width, button_height);
                this.startStopButton.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, button_y + button_id * delta_y);
                this.resetButton.Location = new System.Drawing.Point(this.startStopButton.Location.X + this.startStopButton.Size.Width + Constants.WIDGET_SPACING, button_y + button_id * delta_y);
                this.startStopButton.Font = buttonFont;
                this.resetButton.Font = buttonFont;

            }
        }
        private void OnResizeForm1(object sender, EventArgs ee)
        {

            if ((this.form1.Width > Constants.FORM_MIN_WIDTH) && (this.form1.Height > Constants.FORM_MIN_HEIGHT))
            {

                this.panel1.Width = this.form1.ClientSize.Width;
                this.panel1.Height = this.form1.ClientSize.Height;


                //Intialize Labels 40% of the screen

                int num_rows = (int)((this.wocketsController._Sensors.Count + 2) / 2); //additional row for HR and total sampling rate
                int textBoxHeight = ((int)(0.40 * this.panel1.ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
                int textBoxWidth = ((this.panel1.ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 2);
                int currentTextY = (int)(this.panel1.Height * 0.60);
                int leftTextX = Constants.WIDGET_SPACING;
                int rightTextX = (Constants.WIDGET_SPACING * 2) + textBoxWidth;
                int currentTextX = Constants.WIDGET_SPACING;
                //System.Windows.Forms.Label samplingLabel = (System.Windows.Forms.Label)this.textBoxes[0];
                //samplingLabel.Width = textBoxWidth;
                //samplingLabel.Height = textBoxHeight;
                Form f = new Form();
                f.Width = textBoxWidth;
                f.Height = textBoxHeight;
                Font textFont = GUIHelper.CalculateBestFitFont(f.CreateGraphics(), Constants.MIN_FONT, Constants.MAX_FONT,
                     f.ClientSize, "textBoxAC11", new Font(Constants.FONT_FAMILY, (float)32.0, FontStyle.Bold), (float)0.9, (float)0.9);

                System.Windows.Forms.Label t;
                foreach (Sensor sensor in this.sensors.Sensors)
                {

                    string labelKey = "MITes" + sensor.ID;

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


                //adjust the size of the plotter
                aWocketsPlotter = new WocketsScalablePlotter(this.panel1, WocketsScalablePlotter.DeviceTypes.IPAQ, maxPlots, this.mitesDecoders[0], new Size(this.panel1.Width, (int)(0.60 * this.panel1.Height)));
                SetFormPositions();
                this.isResized = true;
            }
        }

#endif

        #endregion Resize Event Handlers

        #region Click Event Handlers




        private void menuItem1_Click(object sender, EventArgs e)
        {
#if (PocketPC)
            if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
#else
            if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo) == DialogResult.Yes)
#endif
            {
                this.readDataTimer.Enabled = false;                


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




            }



#if (PocketPC)

            Application.Exit();
            System.Diagnostics.Process.GetCurrentProcess().Kill();

#else
                Environment.Exit(0);
#endif
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



        /// <summary>
        /// Report counts for up to three accelerometers, only called when Epoch has new data
        /// </summary>
        public void ReportActivityCounts()
        {

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                int sensor_id = Convert.ToInt32(this.wocketsController._Sensors[i]._ID);
                if (sensor_id > 0)
                {
                    double result = 0;
                    string key = "Wockets " + this.wocketsController._Sensors[i]._ID;
                    if (result == 0)
                        ((System.Windows.Forms.Label)this.sensorLabels[key]).Text = "AC " + sensor_id + ": none";
                    else
                    {
                        ((System.Windows.Forms.Label)this.sensorLabels[key]).Text = "AC " + sensor_id + ": " + Math.Round(result, 2);


                        if (result < 3.0)
                            ((System.Windows.Forms.Label)this.sensorLabels[key]).Text = "AC " + sensor_id + ": still";
                    }

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
                backBuffer = new Bitmap(this.panel1.Width, (int)(this.panel1.Height * 0.60));
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

            if (this.tabControl1.TabIndex == 0)
            {
                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);


            }

        }



        #endregion Graphing functions
        

        #region Timer Methods



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
                if ((this.tabControl1.SelectedIndex == 0) && (isPlotting))
                {
                    GraphAccelerometerValues();
                }

              if (this.wocketsController._CalibrationDirection < 7)
                {
                    System.Windows.Forms.Label t = (System.Windows.Forms.Label)this.sensorLabels["calibration"];
                    t.Text = "X=" + ((int)(this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][0] / this.wocketsController._CalibrationCounter)) +
                             "  Y=" + ((int)(this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][1] / this.wocketsController._CalibrationCounter)) +
                             "  Z=" + ((int)(this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][2] / this.wocketsController._CalibrationCounter));
                }
                if (this.wocketsController._CalibrationCounter >= CALIBRATION_SAMPLES)
                {
                    this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][0] = this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][0] / this.wocketsController._CalibrationCounter;
                    this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][1] = this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][1] / this.wocketsController._CalibrationCounter;
                    this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][2] = this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection][2] / this.wocketsController._CalibrationCounter;
                    this.wocketsController.IsCalibrating = false;
                    this.wocketsController._CalibrationDirection++;
                    this.wocketsController._CalibrationCounter = 0;
                    this.currentIndex = -1;
                    if (this.wocketsController._CalibrationDirection == 7)
                    {
                        this.numOfSamples = this.sampleCounter;
                        this.endTime = DateTime.Now;
                        this.button2.Text = "Quit";
                        this.button2.Visible = true;
                    }
                    else
                    {

                        if (this.wocketsController._CalibrationDirection == 6)
                            this.pictureLabel.Text = "Place the wocket flat on a table";
                        else
                            this.pictureLabel.Text = "Place the wocket as shown";

                        if (this.wocketsController._CalibrationDirection > 0)
                            this.pictureLabel.Text += "\r\nX=" + ((int)this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection - 1][0]) + "  Y=" + ((int)this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection - 1][1]) + "  Z=" + ((int)this.wocketsController._Calibrations[this.wocketsController._CalibrationDirection - 1][2]);

                        this.pictureBox1.Image = this.calibrationImages[this.wocketsController._CalibrationDirection];
                        this.panel2.Visible = true;
                        this.panel1.Visible = false;
                    }
                }
                
            }
        }


        #endregion Timer Methods
    }
}