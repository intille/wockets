using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Threading;
using System.IO;
using Wockets;
using Wockets.Data.Annotation;
using Wockets.Data.Configuration;
using Wockets.Data.Features;
using WocketsAppNS.Utils;
using WocketsAppNS.Utils.Forms.Progress;



namespace WocketsAppNS
{
    public partial class WocketsForm : Form
    {

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


        public WocketsForm()
        {
            InitializeInterface();
        }

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


        private void InitializeDataLogger()
        {
            progressMessage = null;
            aProgressThread = new Thread(new ThreadStart(ProgressThread));
            aProgressThread.Start();
            progressMessage = "Initializing wocket controller\r\n";
            WocketsController wocketsController = this.wocketsControllers[this.selectedWocketController];
            this.annotatedSession = new Session();


            #region Copy configuration files
            progressMessage = "Configuration files... ";
            //copy activity protocol
            if (File.Exists(Constants.ACTIVITY_PROTOCOLS_DIRECTORY + this.aProtocols[this.selectedActivityProtocol]._FileName))
                File.Copy(Constants.ACTIVITY_PROTOCOLS_DIRECTORY + this.aProtocols[this.selectedActivityProtocol]._FileName,
                       this.storageDirectory + "\\ActivityLabelsRealtime.xml");
            else
                throw new Exception("Error: Activity protocol file not found");

            //copy sensor file

            if (File.Exists(Constants.SENSOR_CONFIGURATIONS_DIRECTORY + wocketsController._FileName))
                File.Copy(Constants.SENSOR_CONFIGURATIONS_DIRECTORY + wocketsController._FileName,
                    this.storageDirectory + "\\SensorData.xml");
            else
                throw new Exception("Error: Sensor configuration file not found");

            //copy configuration file
            if (File.Exists(Constants.MASTER_DIRECTORY + "\\Configuration.xml"))
                File.Copy(Constants.MASTER_DIRECTORY + "\\Configuration.xml",
                    this.storageDirectory + "\\Configuration.xml");
            else
                throw new Exception("Error: Configuration file not found");

            //Copy activity summary file
            if (File.Exists(Constants.MASTER_DIRECTORY + "\\ActivitySummary.xml"))
                File.Copy(Constants.MASTER_DIRECTORY + "\\ActivitySummary.xml",
                    this.storageDirectory + "\\ActivitySummary.xml");
            else
                throw new Exception("Error: Activity summary file not found");

            #endregion Copy configuration files

            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Copied\r\nSoftware Configuration ...";

            #region Load Configuration File
            try
            {
                classifierConfiguration = new WocketsConfiguration();
                classifierConfiguration.FromXML(this.storageDirectory + "\\Configuration.xml");                
            }
            catch (Exception e)
            {
                MessageBox.Show("Error: Failed to load classifier configuration. " + e.Message);
            }
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = "Loaded\r\nSensor Configuration ...";

            #endregion Load Feature Extractor

            #region Loading Wockets Configuration (sensors, decoders and receivers)
            //Load the sensor configuration
            try
            {
                wocketsController.FromXML(this.storageDirectory + "\\SensorData.xml");

                //setup where each sensors has to store its data
                for (int i = 0; (i < wocketsController._Sensors.Count); i++)
                {
                    wocketsController._Sensors[i]._RootStorageDirectory = this.storageDirectory + "\\data\\raw\\PLFormat\\";
                    wocketsController._Sensors[i]._Loaded = true;
                }
                CurrentWockets._Controller = wocketsController;    
            }
            catch (Exception e)
            {
                MessageBox.Show("Error: Failed to load sensor data. " + e.Message);
            }
            #endregion Loading Wockets Configuration (sensors, decoders and receivers)

            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Loaded\r\nSession Annotations ...";


            #region Load Activity Annotations
            try
            {
                annotatedSession.FromXML(this.storageDirectory + "\\ActivityLabelsRealtime.xml");
            }
            catch (Exception e)
            {
                MessageBox.Show("Error: Failed to load annotation data. " + e.Message);
            }
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Loaded\r\nClassifier Configuration ...";


            #endregion Load Activity Annotations

            #region Load Feature Extractor
            try
            {
                FullFeatureExtractor.Initialize(CurrentWockets._Controller, this.classifierConfiguration, this.annotatedSession.OverlappingActivityLists[0]);
            }
            catch (Exception e)
            {
                MessageBox.Show("Error: Failed to load classifier configuration. " + e.Message);
            }
            while (progressMessage != null) Thread.Sleep(50);
            progressMessage = " Loaded\r\n";

            #endregion Load Feature Extractor


            progressThreadQuit = true;

            #region Load Data Logger GUI

            #region Initialize GUI Components
            DataLoggerForm dataLoggerForm = new  DataLoggerForm(this.storageDirectory, this.annotatedSession);
            dataLoggerForm.Show();

            #endregion Initialize GUI Components


            #endregion Load Data Logger GUI

        }


       

        private WocketsControllerList wocketsControllers;
        //private WocketsController wocketsController;
        private int selectedWocketController;
        private AnnotationProtocolList aProtocols;
        private int selectedActivityProtocol;
        private string storageDirectory="";
        private Session annotatedSession;
        //private DTConfiguration classifierConfiguration;
        private WocketsConfiguration classifierConfiguration;
        
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

    }
}