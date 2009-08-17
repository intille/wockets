using System;
using System.Collections.Generic;
using System.Xml;
using System.Collections;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Sensors;
using Wockets.Utils;
using Wockets.Data.Commands;
using Wockets.Utils.network;
using Wockets.Exceptions;
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
                                int dataLength = ((Wockets.Receivers.HTCDiamondReceiver)currentReceiver).Read();
                                if (dataLength > 0)
                                {
                                    numDecodedPackets = decoder.Decode(sensor._ID, currentReceiver._Buffer, dataLength);
                                    sensor.Packets += numDecodedPackets;
                                }

                            }
                            else
                                if (sensor._Class == SensorClasses.Wockets)
                                {

                                    CircularBuffer sendBuffer = ((RFCOMMReceiver)currentReceiver)._SBuffer;
                              
                                    #region Write Data
                                    #region Battery Query
                                    batteryPoll[i] -= 1;
                                    if (batteryPoll[i] <= 0)
                                    {


                                        lock (sendBuffer)
                                        {

                                            int availableBytes = GET_BT_CMD._Bytes.Length;
                                            //only insert if the send buffer won't overflow
                                            if ((sendBuffer._Tail + availableBytes) > sendBuffer._Bytes.Length)
                                            {
                                                Buffer.BlockCopy(GET_BT_CMD._Bytes, 0, sendBuffer._Bytes, sendBuffer._Tail, sendBuffer._Bytes.Length - sendBuffer._Tail);
                                                availableBytes -= sendBuffer._Bytes.Length - sendBuffer._Tail;
                                                sendBuffer._Tail = 0;
                                            }
                                            Buffer.BlockCopy(GET_BT_CMD._Bytes, GET_BT_CMD._Bytes.Length - availableBytes, sendBuffer._Bytes, sendBuffer._Tail, availableBytes);
                                            sendBuffer._Tail += availableBytes;
                                        }
                           
                                        batteryPoll[i] = 6000 + i * 200;
                                    }
                                    #endregion Battery Query

                                    #region Alive 
                                    alive[i] -= 1;
                                    if (alive[i] <= 0)
                                    {            
                                        lock (sendBuffer)
                                        {
             
                                            int availableBytes=ALIVE_CMD._Bytes.Length;
                                            //only insert if the send buffer won't overflow
                                            if ((sendBuffer._Tail + availableBytes) > sendBuffer._Bytes.Length)
                                            {
                                                Buffer.BlockCopy(ALIVE_CMD._Bytes, 0, sendBuffer._Bytes, sendBuffer._Tail, sendBuffer._Bytes.Length - sendBuffer._Tail);
                                                availableBytes -= sendBuffer._Bytes.Length - sendBuffer._Tail;
                                                sendBuffer._Tail = 0;
                                            }
                                            Buffer.BlockCopy(ALIVE_CMD._Bytes, ALIVE_CMD._Bytes.Length - availableBytes, sendBuffer._Bytes, sendBuffer._Tail, availableBytes);
                                            sendBuffer._Tail += availableBytes;
                                        }
                                        alive[i] = 200 + i * 10;
                                    }
                                    #endregion Alive
                                    #endregion Write Data

                                    #region Read Data
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
                                    }
                                    #endregion Read Data
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
