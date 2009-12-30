using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Xml;
using System.Threading;

using Wockets;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Sensors;
using Wockets.Utils;
using Wockets.Utils.network;
using Wockets.Data.Commands;
using Wockets.Data.Accelerometers;

using Wockets.Data.Annotation;
using Wockets.Data.Classifiers.Utils;
using Wockets.Exceptions;
using WocketsWeka;
using weka.classifiers;
using Wockets.Applications.Games.Escape;
using weka;
using weka.core;
using weka.classifiers.trees;
using Wockets.Data.Classifiers;
using Wockets.Data.Classifiers.Trees;

namespace Wockets
{
    public sealed class WocketsController : XMLSerializable
    {
        #region Serialization Constants
        private const string SENSORDATA_ELEMENT = "SENSORDATA";
        #endregion Serialization Constants

        private DecoderList decoders;
        private ReceiverList receivers;
        private SensorList sensors;

        private int count = 0;
        public int extractedVectors = 0;
        private int structureFileExamples = 0;
        private string description;
        private string filename;
        private string name;
        private Thread aPollingThread;
        private Thread aSavingThread;
        private Thread aGamingThread;
        private Thread aClassifyingThread;
        private bool polling = false;
        private bool classifying = false;
        private bool training = false;
        private bool saving = false;
        private bool gaming = true;
        private bool isTraining = false;
        private bool isClassifying = false;
        private TextWriter trainingTW = null;
        private TextWriter structureTW = null;
        private Instances instances;
        private WocketsController wocketsController;
        private Classifier classifier;
        private string storageDirectory;
        private Session annotatedSession;
        
        public double StartTime = 0;
        //public Escape _Escape = new Escape();


        /// <summary>
        /// Stores the current record that is being annotated
        /// </summary>
        //private AnnotatedRecord currentRecord;
        public Annotation currentRecord;

        private int calibrationDirection = 0;
        private double[][] calibrations;
        private bool isCalibrating = false;
        private int calibrationCounter = 0;
        private const int CALIBRATION_SAMPLES = 1200;
        private int[][] samples;
        private int currentIndex = -1;
        private double time = 0;

        public bool IsCalibrating
        {
            get
            {
                return this.isCalibrating;
            }
            set
            {
                if (value)
                    this.time = WocketsTimer.GetUnixTime();
                this.isCalibrating = value;
            }
        }

        public int[][] _Samples
        {
            get
            {
                return this.samples;
            }

            set
            {
                this.samples = value;
            }
        }
        public double[][] _Calibrations
        {
            get
            {
                return this.calibrations;
            }
        }

        public int _CalibrationDirection
        {
            get
            {
                return this.calibrationDirection;
            }
            set
            {
                this.calibrationDirection = value;
            }
        }

        public int _CalibrationCounter
        {
            get
            {
                return this.calibrationCounter;
            }
            set
            {
                this.calibrationCounter = value;
            }
        }

        public WocketsController(string name, string filename, string description)
        {
            this.decoders = new DecoderList();
            this.receivers = new ReceiverList();
            this.sensors = new SensorList();
            this.name = name;
            this.filename = filename;
            this.description = description;


            this.calibrations = new double[7][];
            //this.calibrationImages = new Image[7];


            for (int i = 0; (i < 7); i++)
            {
                // this.calibrationImages[i] = (Image)new Bitmap(Constants.CALIBRATIONS_DIRECTORY + "calibration" + (i + 1) + ".gif");
                this.calibrations[i] = new double[3];
            }
            this.samples = new int[CALIBRATION_SAMPLES][];
            for (int i = 0; (i < CALIBRATION_SAMPLES); i++)
                this.samples[i] = new int[3];
        }

        public string _Name
        {
            get
            {
                return this.name;
            }
            set
            {
                this.name = value;
            }
        }

        public string _FileName
        {
            get
            {
                return this.filename;
            }
            set
            {
                this.filename = value;
            }
        }

        public string _Description
        {
            get
            {
                return this.description;
            }

            set
            {
                this.description = value;
            }
        }
        public DecoderList _Decoders
        {
            get
            {
                return this.decoders;
            }
            set
            {
                this.decoders = value;
            }
        }

        public ReceiverList _Receivers
        {
            get
            {
                return this.receivers;
            }
            set
            {
                this.receivers = value;
            }
        }

        public SensorList _Sensors
        {
            get
            {
                return this.sensors;
            }

            set
            {
                this.sensors = value;
            }
        }

        public void Initialize()
        {
            //NetworkStacks._BluetoothStack.Initialize();
            for (int i = 0; (i < this._Receivers.Count); i++)
            {
                try
                {
                    if (this._Sensors[i]._Loaded)
                        this._Receivers[i].Initialize();
                    //this._Receivers[i].
                    //Thread.Sleep(2000);

                }
                catch (Exception e)
                {
                }

            }

            polling = true;
            saving = true;
            //classifying = true;
            //Priorities are very critical to avoid buffer overflow
            aSavingThread = new Thread(new ThreadStart(Save));           
            aSavingThread.Priority = ThreadPriority.Highest;
            aPollingThread = new Thread(new ThreadStart(Poll));
            aPollingThread.Priority = ThreadPriority.Highest;
            aClassifyingThread = new Thread(new ThreadStart(Classify));
            aPollingThread.Start();
            aSavingThread.Start();
            aClassifyingThread.Start();



        }

        public void Dispose()
        {
            saving = false;
            polling = false;
            if (aPollingThread != null)
            {
                aPollingThread.Join();
                aPollingThread.Abort();
            }
            if (aSavingThread != null)
            {
                aSavingThread.Join();
                aSavingThread.Abort();
            }
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
            for (int i = 0; (i < this._Receivers.Count); i++)
            {
                //this._Receivers[i]._Status = ReceiverStatus.Disconnected;
                //Thread.Sleep(100);                
                if (this._Sensors[i]._Loaded)
                {
                    this._Receivers[i].Dispose();
                    Thread.Sleep(1000);
                }
            }

            for (int i = 0; (i < this._Sensors.Count); i++)
                if (this._Sensors[i]._Loaded)
                {
                    this._Sensors[i].Dispose();
                    this._Decoders[i].Dispose();
                }

            
            //NetworkStacks._BluetoothStack.Dispose();

        }

        private void Save()
        {
            while (saving)
            {

                for (int i = 0; (i < this._Sensors.Count); i++)
                {
                    try
                    {

                        this._Sensors[i].Save();
                        Thread.Sleep(1000);
                    }
                    catch (Exception ee)
                    {
                        Logger.Error(ee.Message);
                    }
                }
            }
        }

        public bool Training
        {
            get
            {
                return this.isTraining;
            }
            set
            {
                this.isTraining = value;
            }
        }

        public Annotation _currentRecord
        {
            get
            {
                return this.currentRecord;
            }
            set
            {
                this.currentRecord = value;
            }
        }

        public Session _annotatedSession
        {
            get
            {
                return this.annotatedSession;
            }
            set
            {
                this.annotatedSession = value;
            }
        }

        public string _storageDirectory
        {
            get
            {
                return this.storageDirectory;
            }
            set
            {
                this.storageDirectory = value;
            }
        }

        public Instances _instances
        {
            get
            {
                return this.instances;
            }
            set
            {
                this.instances = value;
            }
        }

        public Classifier _classifier
        {
            get
            {
                return this.classifier;
            }
            set
            {
                this.classifier = value;
            }
        }


        public bool _Classifying
        {
            get
            {
                return this.classifying;
            }
            set
            {
                this.classifying = value;
            }
        }

        public bool _Training
        {
            get
            {
                return this.training;
            }
            set
            {
                this.training = value;
            }
        }

        private void Classify()
        {
            //ClassifierConfiguration configuration = new DTConfiguration();
            //configuration.FromXML(storageDirectory + "\\Configuration.xml");
            //need to pass an activity list that shows all the combinations of activities.
            //for now just have 1 category of activities.            
            //FeatureExtractor.Initialize(this.wocketsController, configuration, this.annotatedSession.OverlappingActivityLists[0]);
            TextWriter trainingTW = null;
            TextWriter structureTW = null;
            int[] labelCounters=null;
            Classifier classifier = null;
            FastVector fvWekaAttributes;
            Instances instances=null;
            string[] activityLabels=null;
            Hashtable labelIndex = new Hashtable(); 
            string arffFileName;
            int classificationCounter = 0;


            while (true)
            {

                if (classifying)
                {
               
                    if (classifier == null)
                    {
                        classifier = new J48();
                        if (!File.Exists("/model.xml"))
                        {
                            string[] arffFiles = Directory.GetFileSystemEntries("/", "output*.arff");
                            if (arffFiles.Length != 1)
                                throw new Exception("Multiple Arff Files in Directory");
                            instances = new Instances(new StreamReader(arffFiles[0]));
                            instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                            classifier.buildClassifier(instances);
                            TextWriter tc = new StreamWriter("/model.xml");
                            classifier.toXML(tc);
                            tc.Flush();
                            tc.Close();
                        }
                        else
                        {
                            instances = new Instances(new StreamReader("/structure.arff"));
                            instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                            classifier.buildClassifier("/model.xml", instances);
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
                    }
                    else
                    {
                        double lastTimeStamp = FeatureExtractor.StoreWocketsWindow();
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

                            if (classificationCounter == 5)
                            {
                                classificationCounter = 0;
                                int mostCount = 0;
                                string mostActivity = "";
                                //Color indicate;
                                //int level;
                                for (int j = 0; (j < labelCounters.Length); j++)
                                {
                                   // level = 240 - 240 * labelCounters[j] / configuration._SmoothWindows;
                                    //indicate = Color.FromArgb(level, level, level);
                                    //this.ActGUIlabels[j].ForeColor = indicate;
                                    //this.ActGUIlabels[j].Invalidate();
                                    if (labelCounters[j] > mostCount)
                                    {
                                        mostActivity = activityLabels[j];
                                        mostCount = labelCounters[j];
                                    }
                                    labelCounters[j] = 0;
                                }

                            }
                        }
                    }
                }

                #region Training

                if (training)
                {
                    //create arff file
                    if (trainingTW == null)
                    {
                        arffFileName ="output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";
                        trainingTW = new StreamWriter(arffFileName);
                        trainingTW.WriteLine("@RELATION wockets");
                        string arffHeader = FeatureExtractor.GetArffHeader();
                        arffHeader += "\n@ATTRIBUTE activity {";
                        int i = 0;
                        for (i = 0; (i < ((this.annotatedSession.OverlappingActivityLists[0]).Count - 1)); i++)
                            arffHeader += this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + ",";
                        arffHeader += this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + "}\n";
                        arffHeader += "\n@DATA\n\n";



                        trainingTW.WriteLine(arffHeader);
                        string structureArffFile = "structure.arff";
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





                Thread.Sleep(50);
            }

        }


        public static object MyLock = new object();

        private void Poll()
        {
            #region Poll All Wockets and MITes and Decode Data
            //CeSetThreadQuantum(new IntPtr(aPollingThread.ManagedThreadId),200);
            //int quantum= CeGetThreadQuantum(new IntPtr(aPollingThread.ManagedThreadId));

            bool allWocketsDisconnected = true;
            bool bluetoothIsReset = false;
            Receiver currentReceiver = null;
            Sensor sensor = null;

            int[] batteryPoll = new int[this._Sensors.Count];
            int[] alive = new int[this._Sensors.Count];

            GET_BT GET_BT_CMD = new GET_BT();
            ALIVE ALIVE_CMD = new ALIVE();
            int pollCounter = 0;
            Logger.Warn("Version 1.15 October 28,2009");
            this.StartTime = WocketsTimer.GetUnixTime();

            while (polling)
            {
                allWocketsDisconnected = true;
                pollCounter++;

                for (int i = 0; (i < this._Sensors.Count); i++)
                {

                    sensor = this._Sensors[i];
                    if (sensor._Loaded)
                    {
                        currentReceiver = sensor._Receiver;
                        try
                        {
                            currentReceiver.Update();


                            if (currentReceiver._Status == ReceiverStatus.Connected)
                            {
                                Decoder decoder = sensor._Decoder;
                                int numDecodedPackets = 0;
                                int tail = currentReceiver._Buffer._Tail;
                                int head = currentReceiver._Buffer._Head;

                                int dataLength = tail - head; //((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail - currentReceiver._Head;
                                if (dataLength < 0)
                                    dataLength = currentReceiver._Buffer._Bytes.Length - head + tail;//((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer.Length - currentReceiver._Head + ((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail;

                                //test if all wockets are disconnected
                                if (sensor._Class == SensorClasses.Wockets)
                                {
                                    if (bluetoothIsReset)
                                        bluetoothIsReset = false;

                                    if (allWocketsDisconnected)
                                        allWocketsDisconnected = false;
                                }

                                if (dataLength > 0)
                                {
                                    if (currentReceiver._Type == ReceiverTypes.HTCDiamond)
                                    {
                                        numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail);
                                        sensor.Packets += numDecodedPackets;
                                    }
                                    else if (sensor._Class == SensorClasses.Wockets)
                                    {

                                        #region Write Data
                                        #region Battery Query
                                        batteryPoll[i] -= 1;
                                        if (batteryPoll[i] <= 0)
                                        {
                                            ((SerialReceiver)currentReceiver).Write(GET_BT_CMD._Bytes);
                                            batteryPoll[i] = 6000 + i * 200;
                                        }
                                        #endregion Battery Query

                                        #region Alive
                                        alive[i] -= 1;
                                        if (alive[i] <= 0)
                                        {
                                            ((SerialReceiver)currentReceiver).Write(ALIVE_CMD._Bytes);
                                            alive[i] =  200;//10 for sniff in continuous worked well
                                        }
                                        #endregion Alive

                                        #endregion Write Data

                                        #region Read Data

                                        numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail); //((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer, head, tail);
                                        currentReceiver._Buffer._Head = tail;//((RFCOMMReceiver)currentReceiver)._Head = tail;
                                        sensor.Packets += numDecodedPackets;
                                        #endregion Read Data


                                        #region Calibration Code

                                        //store sum of abs values of consecutive accelerometer readings                
                                        if ((numDecodedPackets > 0) && (isCalibrating))
                                        {
                                            if (this.calibrationCounter < CALIBRATION_SAMPLES)
                                            {
                                                //currentIndex = 0;
                                                if (this.currentIndex == -1)
                                                    this.currentIndex = decoder._Head;

                                                while ((decoder._Data[currentIndex].UnixTimeStamp >= this.time) && (decoder._Data[currentIndex].Type == Wockets.Data.SensorDataType.ACCEL) && (currentIndex != decoder._Head))
                                                {
                                                    if (this.calibrationCounter == CALIBRATION_SAMPLES)
                                                    {
                                                        this.isCalibrating = false;
                                                        break;
                                                    }


                                                    this.samples[this.calibrationCounter][0] = (int)((AccelerationData)decoder._Data[currentIndex]).X;
                                                    this.samples[this.calibrationCounter][1] = (int)((AccelerationData)decoder._Data[currentIndex]).Y;
                                                    this.samples[this.calibrationCounter][2] = (int)((AccelerationData)decoder._Data[currentIndex]).Z;

                                                    this.calibrations[this.calibrationDirection][0] += (int)((AccelerationData)decoder._Data[currentIndex]).X;
                                                    this.calibrations[this.calibrationDirection][1] += (int)((AccelerationData)decoder._Data[currentIndex]).Y;
                                                    this.calibrations[this.calibrationDirection][2] += (int)((AccelerationData)decoder._Data[currentIndex]).Z;

                                                    this.calibrationCounter++;

                                                    this.time = decoder._Data[currentIndex].UnixTimeStamp;
                                                    currentIndex++;

                                                    if (currentIndex == decoder._Data.Length)
                                                        currentIndex = 0;
                                                }
                                            }

                                        }

                                        #endregion Calibration Code


                                    }

                                    //     if (numDecodedPackets>0)
                                    //        sensor.Save();

                                }

                                if (pollCounter > 2000)
                                {
                                    Logger.Warn("Receiver " + sensor._Receiver._ID + " decoded:" + sensor.Packets + ",saved:" + sensor.SavedPackets + ", tail=" + tail + ",head=" + head);
                                    SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                                    Logger.Debug2(bpower.BatteryLifePercent + "," + bpower.BatteryVoltage + "," + bpower.BatteryCurrent + "," + bpower.BatteryTemperature);
                                    pollCounter = 0;
                                }

                            }

                        }

                        catch (Exception ex)
                        {
                            alive[i] = 200;//10;//200 in continuous worked well
                            Logger.Error(ex.Message + " \nTrace:" + ex.StackTrace);
                            currentReceiver.Dispose();
                        }
                    }
                }

                //reset bluetooth stack once if all wockets are disconnected
                if ((!bluetoothIsReset) && (allWocketsDisconnected)) 
                {
                    Logger.Debug("All Wockets Disconnected. BT Reset.");
                    NetworkStacks._BluetoothStack.Dispose();
                    NetworkStacks._BluetoothStack.Initialize();
                    bluetoothIsReset = true;
                }

                Thread.Sleep(10);
            }



            #endregion Poll All Wockets and MITes and Decode Data
        }

        #region Serialization Methods
        public string ToXML()
        {
            string xml = "<" + SENSORDATA_ELEMENT + ">\n";
            xml += this.receivers.ToXML();
            xml += this.decoders.ToXML();
            xml += this.sensors.ToXML();
            xml += "</" + SENSORDATA_ELEMENT + ">\n";
            return xml;
        }

        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == SENSORDATA_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == ReceiverList.RECEIVERS_ELEMENT)
                        this.receivers.FromXML(jNode.OuterXml);
                    else if (jNode.Name == DecoderList.DECODERS_ELEMENT)
                        this.decoders.FromXML(jNode.OuterXml);
                    else if (jNode.Name == SensorList.SENSORS_ELEMENT)
                    {
                        //the sensor by default loads with a generic decoder as a place holder with its ID set
                        //to point to the right decoder in this.decoders
                        this.sensors.FromXML(jNode.OuterXml);

                        //the decoder references for the sensor have to be updated correctly
                        for (int i = 0; (i < this.sensors.Count); i++)
                            this.sensors[i]._Decoder = this.decoders[this.sensors[i]._Decoder._ID];
                        for (int i = 0; (i < this.sensors.Count); i++)
                            this.sensors[i]._Receiver = this.receivers[this.sensors[i]._Receiver._ID];
                    }
                }
            }
        }
        #endregion Serialization Methods
    }
}
