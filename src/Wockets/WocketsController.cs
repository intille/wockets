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
        private bool polling = false;
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
        public Escape _Escape = new Escape();
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

        public WocketsController(string name,string filename,string description)
        {
            this.decoders = new DecoderList();
            this.receivers = new ReceiverList();
            this.sensors = new SensorList();
            this.name =name;
            this.filename =filename;
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
            aSavingThread = new Thread(new ThreadStart(Save));
            aPollingThread = new Thread(new ThreadStart(Poll));
            aPollingThread.Priority = ThreadPriority.Highest;
            aPollingThread.Start();            
            aSavingThread.Start();

            
         
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
                this._Receivers[i].Dispose();
                Thread.Sleep(1000);
            }

            for (int i = 0; (i < this._Sensors.Count); i++)
                this._Sensors[i].Dispose();         
   
            NetworkStacks._BluetoothStack.Dispose();


        }

        private void Save()
        {
            while (saving)
            {
                try
                {
                    for (int i = 0; (i < this._Sensors.Count); i++)
                    {
                        Thread.Sleep(1000);
                        this._Sensors[i].Save();                        
                    }
                }
                catch (Exception ee)
                {
                    Logger.Error(ee);
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
        public bool _Classifying
        {
            get
            {
                return this.isClassifying;
            }
            set
            {
                this.isClassifying = value;
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

        public static object MyLock = new object();
        
        private void Poll()
        {
            #region Poll All Wockets and MITes and Decode Data
            //CeSetThreadQuantum(new IntPtr(aPollingThread.ManagedThreadId),200);
            //int quantum= CeGetThreadQuantum(new IntPtr(aPollingThread.ManagedThreadId));

            Receiver currentReceiver = null;
            Sensor sensor = null;            

            int[] batteryPoll=new int[this._Sensors.Count];
            int[] alive=new int[this._Sensors.Count];

            GET_BT GET_BT_CMD = new GET_BT();
            ALIVE ALIVE_CMD = new ALIVE();

            while (polling)
            {

                #region Receiver Reconnection Code
#if (PocketPC)
                /*
                for (int i = 0; (i < this._Receivers.Count); i++)
                {
                    if (this._Receivers[i]._Running==false)                     
                        this._Receivers[i].BeginReconnect();
                    if ((this._Receivers[i]._Running == true) && (this._Receivers[i]._Reconnecting == true))
                        this._Receivers[i].EndReconnect();
                }*/


#endif
                #endregion Receiver Reconnection Code

                try
                {
                    for (int i = 0; (i < this._Sensors.Count); i++)
                    {
                        sensor = this._Sensors[i];
                        currentReceiver = sensor._Receiver;
                        currentReceiver.Update();

                        if (currentReceiver._Status == ReceiverStatus.Connected)
                        {
                            Decoder decoder = sensor._Decoder;
                            int numDecodedPackets = 0;
                            if (currentReceiver._Type == ReceiverTypes.HTCDiamond)
                            {
                                //int dataLength = ((Wockets.Receivers.HTCDiamondReceiver)currentReceiver).Read();
                                int dataLength = currentReceiver._Buffer._Tail - currentReceiver._Buffer._Head; //((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail - currentReceiver._Head;
                                if (dataLength < 0)
                                    dataLength = currentReceiver._Buffer._Bytes.Length - currentReceiver._Buffer._Head + currentReceiver._Buffer._Tail;//((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer.Length - currentReceiver._Head + ((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail;
                                if (dataLength > 0)
                                {
                                    //numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer._Bytes, dataLength);
                                    numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer); 
                                    sensor.Packets += numDecodedPackets;
                                }

                            }
                            else
                                if (sensor._Class == SensorClasses.Wockets)
                                {

                                    //CircularBuffer sendBuffer = ((RFCOMMReceiver)currentReceiver)._SBuffer;
                              
                                    #region Write Data
                                    #region Battery Query
                                    /*batteryPoll[i] -= 1;
                                    if (batteryPoll[i] <= 0)
                                    {
                                        ((SerialReceiver)currentReceiver).Write(GET_BT_CMD._Bytes);
                                        batteryPoll[i] = 6000 + i * 200;
                                    }*/
                                    #endregion Battery Query

                                    #region Alive 
                                    alive[i] -= 1;
                                    if (alive[i] <= 0)
                                    {            
                                        ((SerialReceiver)currentReceiver).Write(ALIVE_CMD._Bytes);
                                        alive[i] = 2000;// + i * 10;
                                    }
                                    #endregion Alive


                      
                                    #endregion Write Data

                                    #region Read Data

                                    int dataLength = currentReceiver._Buffer._Tail - currentReceiver._Buffer._Head; //((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail - currentReceiver._Head;
                                    if (dataLength < 0)
                                        dataLength = currentReceiver._Buffer._Bytes.Length - currentReceiver._Buffer._Head + currentReceiver._Buffer._Tail;//((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer.Length - currentReceiver._Head + ((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail;
                                    if (dataLength > 0)
                                    {
                                        int tail = currentReceiver._Buffer._Tail;//((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail;
                                        int head = currentReceiver._Buffer._Head;//currentReceiver._Head;
                                        numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer); //((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer, head, tail);
                                        currentReceiver._Buffer._Head = tail;//((RFCOMMReceiver)currentReceiver)._Head = tail;
                                        sensor.Packets += numDecodedPackets;
                                    }
                                    /*
                                    int dataLength = currentReceiver._Tail - currentReceiver._Head;
                                    if (dataLength < 0)
                                        dataLength = currentReceiver._Buffer.Length - currentReceiver._Head + currentReceiver._Tail;
                                    if (dataLength > 0)
                                    {
                                        int tail = currentReceiver._Tail;
                                        int head = currentReceiver._Head;
                                        numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail);
                                        ((RFCOMMReceiver)currentReceiver)._Head = tail;
                                        sensor.Packets += numDecodedPackets;
                                    }*/
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

                                            while ((decoder._Data[currentIndex].UnixTimeStamp >= this.time) && (decoder._Data[currentIndex].Type== Wockets.Data.SensorDataType.ACCEL) && (currentIndex != decoder._Head))
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


                                    
                                    #region Training

                                    if (Training)
                                    {
                                        //create arff file
                                        if (trainingTW == null)
                                        {
                                            string arffFileName = this._storageDirectory+ "\\output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";                   
                                            trainingTW = new StreamWriter(arffFileName);                    
                                            trainingTW.WriteLine("@RELATION wockets");
                                            string arffHeader = FeatureExtractor.GetArffHeader();
                                            arffHeader += "\n@ATTRIBUTE activity {";
                                            int j = 0;
                                            for (j = 0; (j < ((this._annotatedSession.OverlappingActivityLists[0]).Count - 1)); j++)
                                                arffHeader+=this._annotatedSession.OverlappingActivityLists[0][j]._Name.Replace(' ', '_') + ",";
                                            arffHeader+=this._annotatedSession.OverlappingActivityLists[0][j]._Name.Replace(' ', '_') + "}\n";
                                            arffHeader+="\n@DATA\n\n";
                                            
                                            
                                            
                                            trainingTW.WriteLine(arffHeader);
                                            string structureArffFile = this._storageDirectory + "\\structure.arff";
                                            structureTW = new StreamWriter(structureArffFile);
                                            structureTW.WriteLine("@RELATION wockets");
                                            structureTW.WriteLine(arffHeader);

                                        }
                                        string current_activity = "unknown";
                                        lock (MyLock)
                                        {
                                            if (this._currentRecord != null)
                                            {
                                                double lastTimeStamp = FeatureExtractor.StoreWocketsWindow();
                                                if (FeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                                                {
                                                    current_activity = this._currentRecord.Activities._CurrentActivity;
                                                    string arffSample = FeatureExtractor.toString() + "," + current_activity;
                                                    trainingTW.WriteLine(arffSample);
                                                    if (count < 5)
                                                    {
                                                        count++;
                                                        structureTW.WriteLine(arffSample);
                                                    }
                                                    extractedVectors++;
                                                    if (structureFileExamples < 10)
                                                    {
                                                        structureTW.WriteLine(arffSample);
                                                        structureFileExamples++;
                                                    }
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

                                    #region Classifying

                                    if (this._Classifying)
                                    {
                                        double lastTimeStamp = FeatureExtractor.StoreWocketsWindow();//WocketsTimer.LastTimeStamp;//WocketsTimer.FeatureExtractor.StoreMITesWindow();
                                        if (FeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                                        {
                                            Instance newinstance = new Instance(this._instances.numAttributes());
                                            newinstance.Dataset = this._instances;
                                            for (int j = 0; (j < FeatureExtractor.Features.Length); j++)
                                                newinstance.setValue(this._instances.attribute(j), FeatureExtractor.Features[j]);
                                            double predicted = classifier.classifyInstance(newinstance);
                                            string predicted_activity = newinstance.dataset().classAttribute().value_Renamed((int)predicted);
                                            this._Escape._Move = predicted_activity;
                                        }
                                    }

                                    #endregion Classifying

                                }
                        }
                    }

                }
                catch (BurstyException be)
                {
                    Logger.Warn("Bursty Data," + sensor._ID + "," + be.Message);
                    currentReceiver.Dispose();
                }
                catch (Exception ex)
                {
                    Logger.Warn("Disconnection," + sensor._ID+","+ex.Message);
                    currentReceiver.Dispose();
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
