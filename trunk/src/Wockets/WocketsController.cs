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
using Wockets.Data.Features;


using WocketsWeka;
using weka.classifiers;
using weka;
using weka.core;
using weka.classifiers.trees;


namespace Wockets
{
    /// <summary>
    /// The wockets controller is the starting point to talk to the wockets. It instantiates a number of threads to do the following:
    /// 1- read data 2- save data 3- extract features and classify data into activities 4- transparently managing, tracking and updating
    /// the status of connections to wockets 
    /// </summary>
    public sealed class WocketsController : XMLSerializable
    {                
        #region Serialization Constants
        private const string SENSORDATA_ELEMENT = "SENSORDATA";
        #endregion Serialization Constants

        #region Wockets Controller Information
        public string _Description;
        public string _Filename;
        public string _Name;
        #endregion Wockets Controller Information

        #region Wockets controller components
        public ReceiverList _Receivers;
        public DecoderList _Decoders;        
        public SensorList _Sensors;
        #endregion Wockets controller components

        #region Threads instantiated by the controller
        
        /// <summary>
        /// Handle to the data polling thread
        /// </summary>
        private Thread aPollingThread;

        /// <summary>
        /// Handle to the data saving thread
        /// </summary>
        private Thread aSavingThread;

        /// <summary>
        /// Handle to the classification thread
        /// </summary>
        private Thread aClassifyingThread;
        #endregion Threads instantiated by the controller


        public int extractedVectors = 0;
        private int structureFileExamples = 0;


        private AutoResetEvent waitToPollEvent;
        private AutoResetEvent pollingEvent;
        private bool polling = true;

        private AutoResetEvent savingEvent;
        private AutoResetEvent waitToSaveEvent;
        private bool saving = true;

        private AutoResetEvent classifyingEvent;
        private bool classifying = false;        
        private AutoResetEvent trainingEvent;
        private bool training = false;        
        private TextWriter trainingTW = null;
        private TextWriter structureTW = null;
        private Instances instances;        
        private Classifier classifier;
        private string storageDirectory;
        private Session annotatedSession;
        
        public double StartTime = 0;


        /// <summary>
        /// Stores the current record that is being annotated
        /// </summary>
        //private AnnotatedRecord currentRecord;
        public Annotation currentRecord;

           
        public bool _Bursty = false;
        private ManualResetEvent paused;
        public bool _Paused = false;

        /// <summary>
        /// A property that controls the data saving thread. When set to true the saving thread is signaled to run.
        /// When set to false it is guruanteed that the saving thread will be stopped prior to the call returning to avoid race
        /// conditions
        /// </summary>
        public bool _Saving
        {
            get
            {
                return this.saving;
            }
            set
            {
                this.saving = value;
                // if saving is true then wakeup the saving thread
                if (value)
                    this.savingEvent.Set();
                else //if saving is false then block until saving is done.
                    this.waitToSaveEvent.WaitOne();                                
            }
        }

        public bool _Polling
        {
            get
            {
                return this.polling;
            }
            set
            {               
                this.polling = value;
                if (value)
                    this.pollingEvent.Set();
                else
                    this.waitToPollEvent.WaitOne();                
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
                if (value)
                    this.trainingEvent.Set();
                this.training = value;
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
                if (value)
                    this.classifyingEvent.Set();
                this.classifying = value;
            }
        }



        public WocketsController(string name, string filename, string description)
        {

            this._Name = name;
            this._Filename = filename;
            this._Description = description;


            this.paused = new ManualResetEvent(false);
            
            this.savingEvent = new AutoResetEvent(false);
            this.waitToSaveEvent = new AutoResetEvent(false);

            this.pollingEvent = new AutoResetEvent(false);
            this.waitToPollEvent = new AutoResetEvent(false);
            this.classifyingEvent = new AutoResetEvent(false);
            this.trainingEvent = new AutoResetEvent(false);

            this._Decoders = new DecoderList();
            this._Receivers = new ReceiverList();
            this._Sensors = new SensorList();
                     
        }
  
        public void Initialize()
        {
            //NetworkStacks._BluetoothStack.Initialize();
            for (int i = 0; (i < this._Receivers.Count); i++)
            {
                try
                {
                    if (this._Sensors[i]._Loaded)
                    {
                        this._Receivers[i].Initialize();
                        this._Decoders[i].Initialize();
                    }

                    if (this._Receivers[i]._Type == ReceiverTypes.RFCOMM)
                        ((RFCOMMReceiver)this._Receivers[i])._Bursty = this._Bursty;
                    //this._Receivers[i].
                    //Thread.Sleep(2000);

                }
                catch (Exception e)
                {
                }

            }

            polling = true;
            classifying = true;
            
            //Priorities are very critical to avoid buffer overflow
           
            
 
            aPollingThread = new Thread(new ThreadStart(Poll));
            aPollingThread.Priority = ThreadPriority.Highest;
            //aClassifyingThread = new Thread(new ThreadStart(Classify));
            // aClassifyingThread.Start();

            aPollingThread.Start();
           

            //selene commented it out for power test

            if (!_Bursty)
            {
                _Saving = true;
                aSavingThread = new Thread(new ThreadStart(Save));
                aSavingThread.Priority = ThreadPriority.Highest;
                aSavingThread.Start();
            }
            

        }


        public void Unpause()
        {
            _Paused = false;
            this.paused.Set();
        }

        public void Pause()
        {
            this.paused.Reset();
            _Paused = true;
        }
        
 
        

           

        public void Dispose()
        {


            if (aPollingThread != null)
            {
                polling = false;
                aPollingThread.Join();
                aPollingThread.Abort();
            }

            if (aSavingThread != null)
            {
                _Saving = false;
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
            while (true)
            {
                if (!this.saving)
                {
                    this.waitToSaveEvent.Set();
                    this.savingEvent.WaitOne();
                }

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



        private void Train()
        {

            TextWriter trainingTW = null;
            TextWriter structureTW = null;
            Hashtable labelIndex = new Hashtable();
            string arffFileName;

            while (true)
            {

                if (!this.training)
                    this.trainingEvent.WaitOne();


                #region Training
                //create arff file
                if (trainingTW == null)
                {
                    arffFileName = "output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";
                    trainingTW = new StreamWriter(arffFileName);
                    trainingTW.WriteLine("@RELATION wockets");
                    string arffHeader = FullFeatureExtractor.GetArffHeader();
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
                    double lastTimeStamp = FullFeatureExtractor.StoreWocketsWindow();
                    if (FullFeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                    {
                        current_activity = this.currentRecord.Activities._CurrentActivity;
                        string arffSample = FullFeatureExtractor.toString() + "," + current_activity;
                        trainingTW.WriteLine(arffSample);
                        extractedVectors++;
                        if (structureFileExamples < 10)
                        {
                            structureTW.WriteLine(arffSample);
                            structureFileExamples++;
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

        private void Classify()
        {
            int[] labelCounters = null;
            Classifier classifier = null;
            FastVector fvWekaAttributes;
            Instances instances = null;
            string[] activityLabels = null;
            Hashtable labelIndex = new Hashtable();         
            int classificationCounter = 0;


            while (true)
            {

                if (!this.classifying)
                    this.classifyingEvent.WaitOne();

                if (classifier == null)
                {
                    classifier = new J48();
                    if (!File.Exists("/model.xml"))
                    {
                        string[] arffFiles = Directory.GetFileSystemEntries("/", "output*.arff");
                        if (arffFiles.Length != 1)
                            throw new Exception("Multiple Arff Files in Directory");
                        instances = new Instances(new StreamReader(arffFiles[0]));
                        instances.Class = instances.attribute(FullFeatureExtractor.ArffAttributeLabels.Length);
                        classifier.buildClassifier(instances);
                        TextWriter tc = new StreamWriter("/model.xml");
                        classifier.toXML(tc);
                        tc.Flush();
                        tc.Close();
                    }
                    else
                    {
                        instances = new Instances(new StreamReader("/structure.arff"));
                        instances.Class = instances.attribute(FullFeatureExtractor.ArffAttributeLabels.Length);
                        classifier.buildClassifier("/model.xml", instances);
                    }


                    fvWekaAttributes = new FastVector(FullFeatureExtractor.ArffAttributeLabels.Length + 1);
                    for (int i = 0; (i < FullFeatureExtractor.ArffAttributeLabels.Length); i++)
                        fvWekaAttributes.addElement(new weka.core.Attribute(FullFeatureExtractor.ArffAttributeLabels[i]));

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
                    double lastTimeStamp = FullFeatureExtractor.StoreWocketsWindow();
                    if (FullFeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                    {
                        Instance newinstance = new Instance(instances.numAttributes());
                        newinstance.Dataset = instances;
                        for (int i = 0; (i < FullFeatureExtractor.Features.Length); i++)
                            newinstance.setValue(instances.attribute(i), FullFeatureExtractor.Features[i]);
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
            Logger.Warn("Version "+CurrentWockets._Version+" "+CurrentWockets._Date);
            this.StartTime = WocketsTimer.GetUnixTime();

            while (true)
            {

              /* if ((_Bursty) && (_Paused))
                {
                    for (int i = 0; (i < this._Sensors.Count); i++)
                    {
                        //this._Sensors[i].Save();
                        this._Sensors[i]._ReceivedPackets = 0;
                        this._Sensors[i]._SavedPackets = 0;
                        this._Receivers[i]._Status = Wockets.Receivers.ReceiverStatus.Disconnected;
                    }
                    this.paused.WaitOne();
                }*/
               

                if (!polling)
                {


                    this.waitToPollEvent.Set();
                    for (int i = 0; (i < this._Sensors.Count); i++)
                    {
                        this._Sensors[i]._ReceivedPackets = 0;
                        this._Sensors[i]._SavedPackets = 0;
                        //this._Receivers[i]._Status = Wockets.Receivers.ReceiverStatus.Disconnected;
                        this._Receivers[i].Dispose();

                    }
                    this.pollingEvent.WaitOne();
                }

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
                            if (_Bursty)
                            {
                                if (sensor._ReceivedPackets< 2400)
                                    currentReceiver.Update();
                                else
                                    continue;
                            }
                            else
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
                                        sensor._ReceivedPackets += numDecodedPackets;
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
                                            //if (((RFCOMMReceiver)currentReceiver)._Tsniff == Wockets.Utils.network.Bluetooth.TSniff.Continuous)
                                                alive[i] = 200;//10 for sniff, 200 in continuous worked well
                                            //else
                                             //   alive[i] = 10;
                                            //if (((RFCOMMReceiver)currentReceiver)._Tsniff== Wockets.Utils.network.Bluetooth.TSniff.Sniff2Seconds)
                                        }
                                        #endregion Alive

                                        #endregion Write Data

                                        #region Read Data

                                        numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail); //((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer, head, tail);
                                        currentReceiver._Buffer._Head = tail;//((RFCOMMReceiver)currentReceiver)._Head = tail;
                                        sensor._ReceivedPackets += numDecodedPackets;
                                        #endregion Read Data
                                    }

                                    //     if (numDecodedPackets>0)
                                    //        sensor.Save();

                                }

                                if (pollCounter > 2000)
                                {
                                    Logger.Warn("Receiver " + sensor._Receiver._ID + " decoded:" + sensor._ReceivedPackets + ",saved:" + sensor._SavedPackets + ", tail=" + tail + ",head=" + head);
                                    pollCounter = 0;
                                }

                            }

                        }

                        catch (Exception ex)
                        {
                            alive[i] = 200;//10 in sniff//200 in continuous worked well
                            Logger.Error(ex.Message + " \nTrace:" + ex.StackTrace);
                            currentReceiver.Dispose();
                        }
                    }
                }

                //reset bluetooth stack once if all wockets are disconnected

                if ((!_Bursty) && (!bluetoothIsReset) && (allWocketsDisconnected))
                {
                    try
                    {
                        if (CurrentWockets._Configuration._SoftwareMode == Wockets.Data.Configuration.SoftwareConfiguration.DEBUG)
                            Logger.Debug("All Wockets Disconnected. BT Reset.");
                        NetworkStacks._BluetoothStack.Dispose();
                        NetworkStacks._BluetoothStack.Initialize();
                        bluetoothIsReset = true;
                    }
                    catch
                    {
                    }
                }

                Thread.Sleep(10);
            }



            #endregion Poll All Wockets and MITes and Decode Data
        }

        #region Serialization Methods
        public string ToXML()
        {
            string xml = "<" + SENSORDATA_ELEMENT + ">\n";
            xml += this._Receivers.ToXML();
            xml += this._Decoders.ToXML();
            xml += this._Sensors.ToXML();
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
                        this._Receivers.FromXML(jNode.OuterXml);
                    else if (jNode.Name == DecoderList.DECODERS_ELEMENT)
                        this._Decoders.FromXML(jNode.OuterXml);
                    else if (jNode.Name == SensorList.SENSORS_ELEMENT)
                    {
                        //the sensor by default loads with a generic decoder as a place holder with its ID set
                        //to point to the right decoder in this.decoders
                        this._Sensors.FromXML(jNode.OuterXml);

                        //the decoder references for the sensor have to be updated correctly
                        for (int i = 0; (i < this._Sensors.Count); i++)
                            this._Sensors[i]._Decoder = this._Decoders[this._Sensors[i]._Decoder._ID];
                        for (int i = 0; (i < this._Sensors.Count); i++)
                            this._Sensors[i]._Receiver = this._Receivers[this._Sensors[i]._Receiver._ID];
                    }
                }
            }
        }
        #endregion Serialization Methods
    }
}
