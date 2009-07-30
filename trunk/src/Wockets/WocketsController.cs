using System;
using System.Collections.Generic;
using System.Xml;
using System.Collections;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Sensors;
using Wockets.Utils;
using Wockets.Utils.network;
using System.Threading;

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

        private string description;
        private string filename;
        private string name;
        private Thread aPollingThread;
        private Thread aSavingThread;
        private bool polling = false;
        private bool saving = false;

        public WocketsController(string name,string filename,string description)
        {
            this.decoders = new DecoderList();
            this.receivers = new ReceiverList();
            this.sensors = new SensorList();
            this.name =name;
            this.filename =filename;
            this.description = description;
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
                        this._Sensors[i].Save();
                        Thread.Sleep(50);
                    }
                }
                catch (Exception ee)
                {
                    Logger.Error(ee);
                }

            }
        }

  
        private void Poll()
        {
            #region Poll All Wockets and MITes and Decode Data
            //CeSetThreadQuantum(new IntPtr(aPollingThread.ManagedThreadId),200);
            //int quantum= CeGetThreadQuantum(new IntPtr(aPollingThread.ManagedThreadId));

            Receiver currentReceiver = null;
            Sensor sensor = null;
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
                        currentReceiver = this._Receivers[sensor._Receiver];
                        if (currentReceiver._Status == ReceiverStatus.Connected)
                        {
                            Decoder decoder = sensor._Decoder;
                            int numDecodedPackets = 0;
                            if (currentReceiver._Type == ReceiverTypes.HTCDiamond)
                            {
                                int dataLength = ((Wockets.Receivers.HTCDiamondReceiver)currentReceiver).Read();
                                if (dataLength > 0)                                
                                    numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, dataLength);                                
                            }
                            else
                                if (sensor._Class == SensorClasses.Wockets)
                                {
                                    
                                    int dataLength = currentReceiver._Tail - currentReceiver._Head;
                                    if (dataLength < 0)
                                        dataLength = currentReceiver._Buffer.Length - currentReceiver._Head + currentReceiver._Tail;
                                    if (dataLength > 0)
                                    {
                                        int tail = currentReceiver._Tail;
                                        int head = currentReceiver._Head;
                                        numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, head, tail);
                                        ((RFCOMMReceiver)currentReceiver)._Head = tail;
                                    }
                                }

                            
                        }
                    }
//                    if (isPlotting)
  //                      UpdateGraph();

                }
                //Thrown when there is a Bluetooth failure                    
                //TODO: Make sure no USB failure happening
                catch (Exception ex)
                {
                   // if (sensor._Class == SensorClasses.Wockets)
                    //{


                        Logger.Warn("Wocket " + sensor._ID + " has disconnected.");
                        //this.disconnected[sensor._ID] = 1;

                        //if (this.bluetoothConnectors[currentReceiver._ID] == null)
                        //{
                         //   this.bluetoothConnectors[currentReceiver._ID] = new BluetoothConnector(currentReceiver, this);
                        //}
                        
                        currentReceiver.Dispose();
                    //}
                   // else if (sensor._Class == SensorClasses.HTCDiamondTouch)
                    //{
                      //  currentReceiver.Initialize();
                       // currentReceiver._Running = true;
                    //}
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
                    }
                }
            }
        }
        #endregion Serialization Methods
    }
}
