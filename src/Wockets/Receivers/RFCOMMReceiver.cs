using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.Xml;
using System.IO;
using System.Net.Sockets;
using System.IO.Ports;
using System.Diagnostics;
//using HousenCS.SerialIO;
using System.Runtime.InteropServices;
using System.Threading;
using Wockets.Utils;
using Wockets.Data.Configuration;
using System.Net;
using Microsoft.Win32;
using Wockets.Utils.network;
using Wockets.Utils.network.Bluetooth;
using Wockets.Utils.network.Bluetooth.Microsoft;
using Wockets.Utils.network.Bluetooth.Widcomm;
using Wockets.Data.Types;
using Wockets.Data.Commands;


namespace Wockets.Receivers
{
    public sealed class RFCOMMReceiver : SerialReceiver
    {
        #region Serialization Constants
        private const string RFCOMM_TYPE = "RFCOMM";
        private const string MACADDRESS_ATTRIBUTE = "MacAddress";
        private const string PIN_ATTRIBUTE = "PIN";
        private const string TSNIFF_ATTRIBUTE = "TSniff";
        #endregion Serialization Constants
        //RFCOMM Configuration
        private const bool USE_PARITY = false;
        private const bool USE_STOP_BIT = true;
        private const int BAUD_RATE = 57600;
        private const int BUFFER_SIZE = 8192;//8000;
        private const int SEND_BUFFER_SIZE = 256;
        private const int PORT_NUMBER = 9;
        private const int MAXIMUM_SAMPLING_RATE = 70;

        //RFCOMM Specific Objects

        //private BluetoothStream bluetoothStream;       

        public BluetoothStream bluetoothStream;
        private const int MAC_SIZE = 6;
        private string address;
        private byte[] address_bytes;
        private string pin;
        private int sniffTime = 0;
        private bool sniffMode;
        public CircularBuffer _SBuffer;
        
        //Default
        public TransmissionMode _TMode = TransmissionMode.Continuous;
        public bool _TimeoutEnabled = true;
        public double _ConnectionTime = 0;
        public double _CurrentConnectionUnixTime = 0;
        public int _Reconnections = 0;
        public int _SuccessfulConnections = 0;
     

        public override int CompareTo(object receiver)
        {
            if (receiver is RFCOMMReceiver)
                return this._Address.CompareTo(((RFCOMMReceiver)receiver)._Address);
            else
                return base.CompareTo(receiver);
        }

        public RFCOMMReceiver()
            : base(BUFFER_SIZE)
        {
            this.type = ReceiverTypes.RFCOMM;
            this._SBuffer = new CircularBuffer(SEND_BUFFER_SIZE);        
        }

   


        #region Access Properties


        public byte[] _AddressBytes
        {
            get
            {
                return this.address_bytes;
            }
        }
        public string _Address
        {
            get
            {

                return this.address;
            }
            set
            {
                this.address = value;
                this.address_bytes = new byte[MAC_SIZE];
                for (int i = 0; (i < MAC_SIZE); i++)
                    this.address_bytes[i] = (byte)(System.Int32.Parse(address.Substring(i * 2, 2), System.Globalization.NumberStyles.AllowHexSpecifier) & 0xff);
            }
        }
        public string _PIN
        {
            get
            {
                return this.pin;
            }
        }

        public int _TSNIFF
        {
            get
            {
                return this.sniffTime;
            }

            set
            {
                this.sniffTime = value;
            }
        }

        public override bool _Running
        {
            get
            {
                return this.isRunning;
            }
            set
            {
                this.isRunning = value;
            }
        }
   
        
        public override void Update()
        {
            lock (this)
            {
                /// If a disconnection is detected for the bluetooth stream, update the status of the
                /// receiver and flush the send buffer and delete references to the bluetooth stream
                if ((this.bluetoothStream != null) && (this.bluetoothStream._Status == BluetoothStatus.Disconnected))
                {
                    
                    this.bluetoothStream = null;                    
                    this.status = ReceiverStatus.Disconnected;
                    this._SBuffer._Head = 0;
                    this.ndisc++;
                    this.disconnectionTime = WocketsTimer.GetUnixTime();
                }

                // If the bluetooth stream is null or the receiver is not reconnecting
                // then instantiate a thread to reconnect
                if ((this.bluetoothStream == null) && (this.status != ReceiverStatus.Reconnecting))
                {
                    this.status = ReceiverStatus.Reconnecting;
                    reconnectionThread = new Thread(new ThreadStart(this.Reconnect));
                    reconnectionThread.Start();
                    if (CurrentWockets._Configuration._SoftwareMode == SoftwareConfiguration.DEBUG)
                        Logger.Debug("RFCOMMReceiver: Update: Spawning a reconnection thread for "+ this._Address);
                }

                if ((this.status != ReceiverStatus.Connected) && (this.bluetoothStream != null) && (this.bluetoothStream._Status == BluetoothStatus.Connected))
                {
                    if (this.status == ReceiverStatus.Reconnecting)
                    {                        
                        reconnectionThread.Join();
                        reconnectionThread.Abort();
                        reconnectionThread = null;            
                    }
                   if (CurrentWockets._Configuration._SoftwareMode == SoftwareConfiguration.DEBUG)                           
                       Logger.Debug("RFCOMMReceiver: Update: Reconnection successful for "+ this._Address);
                    this.status = ReceiverStatus.Connected;
                    if (this.disconnectionTime!=0)                    
                        this.disconTime += (int)((WocketsTimer.GetUnixTime() - this.disconnectionTime) / 1000);
                }
            }
        }

        public override ReceiverStatus _Status
        {
            get
            {

                return this.status;
            }
            set
            {
                this.status = value;
            }
        }
        #endregion Access Properties



        private void Reconnect()
        {
            Random random = new Random();
            int backoff = random.Next(1000);
            _Reconnections = 0;
            if (this._TMode== TransmissionMode.Continuous)
              Thread.Sleep(10000);       

            
            while ((this.bluetoothStream == null) || (this.bluetoothStream._Status != BluetoothStatus.Connected))
            {
                Thread.Sleep(backoff);
                if (this.Initialize())
                {
                    if (CurrentWockets._Configuration._SoftwareMode == SoftwareConfiguration.DEBUG)
                        Logger.Debug("RFCOMMReceiver: Reconnect: Reconnection succeeded " + this._Address);
                }
                else
                {
                    _Reconnections++;
                   /* if (_Reconnections == 5) //after 20 attempts
                        backoff = 1000 + random.Next(10000);
                    else if (_Reconnections == 30)
                        backoff = 10000 + random.Next(20000);
                    else if (_Reconnections == 100)
                        backoff = 60000 + random.Next(10000);   */                
                }

                
            }
        }

        public override bool Initialize()
        {
            
            try
            {               
                this._Buffer = new CircularBuffer(this._Buffer._Bytes.Length);
                this.head = 0;
                this._SBuffer = new CircularBuffer(SEND_BUFFER_SIZE);

                //Always set the transmission mode on connection
                Write(new SET_VTM(this._TMode)._Bytes);
                if (CurrentWockets._Configuration._SoftwareMode == Wockets.Data.Configuration.SoftwareConfiguration.DEBUG)
                    Logger.Debug("RFCOMMReceiver: Initialize: Attempting reconnection for receiver " + this._Address);
                this.bluetoothStream = NetworkStacks._BluetoothStack.Connect(this._Buffer,this._SBuffer , this.address_bytes, this.pin);              
                if (this.bluetoothStream == null)
                    return false;

                if (this._TMode== TransmissionMode.Bursty60)
                    this.bluetoothStream._Timeout = 2;
                this.bluetoothStream._TimeoutEnabled = this._TimeoutEnabled;
                this._ConnectionTime = this.bluetoothStream._ConnectionTime;
                this._CurrentConnectionUnixTime = this.bluetoothStream._CurrentConnectionUnixTime;
                this._SuccessfulConnections++;
                return true;
            }
            catch (Exception e)
            {
                return false;
            }
        }


        public override void Write(byte[] data)
        {
            lock (this._SBuffer)
            {

                int availableBytes = data.Length;
                //only insert if the send buffer won't overflow
                if ((this._SBuffer._Tail + availableBytes) > this._SBuffer._Bytes.Length)
                {
                    Buffer.BlockCopy(data, 0, this._SBuffer._Bytes, this._SBuffer._Tail, this._SBuffer._Bytes.Length - this._SBuffer._Tail);
                    availableBytes -= this._SBuffer._Bytes.Length - this._SBuffer._Tail;
                    this._SBuffer._Tail = 0;
                }
                Buffer.BlockCopy(data, data.Length - availableBytes, this._SBuffer._Bytes, this._SBuffer._Tail, availableBytes);
                this._SBuffer._Tail += availableBytes;
            }
            
        }

        public override bool Dispose()
        {
            try
            {
                if (this.reconnectionThread != null)
                    this.reconnectionThread.Abort(); 
                if (this.bluetoothStream!=null)
                    this.bluetoothStream._Status = BluetoothStatus.Disconnected;
                this._Status = ReceiverStatus.Disconnected;
                this._Reconnections = 0;
                this._SuccessfulConnections = 0;
                return true;
            }
            catch (Exception)
            {
                return false;
            }
        }

        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + RFCOMMReceiver.RECEIVER_ELEMENT + " ";
            xml += RFCOMMReceiver.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += RFCOMMReceiver.TYPE_ATTRIBUTE + "=\"" + RFCOMMReceiver.RFCOMM_TYPE + "\" ";
            xml += RFCOMMReceiver.MACADDRESS_ATTRIBUTE + "=\"" + this.address + "\" ";
            xml += RFCOMMReceiver.PIN_ATTRIBUTE + "=\"" + this.pin + "\" ";
            xml += RFCOMMReceiver.TSNIFF_ATTRIBUTE + "=\"" + this.sniffTime + "\" ";
            xml += RFCOMMReceiver.PORT_NUMBER_ATTRIBUTE + "=\"" + this._PortNumber + "\" ";
            xml += RFCOMMReceiver.PARITY_ATTRIBUTE + "=\"" + this._Parity + "\" ";
            xml += RFCOMMReceiver.STOPBIT_ATTRIBUTE + "=\"" + this._StopBit + "\" ";
            xml += RFCOMMReceiver.BAUD_RATE_ATTRIBUTE + "=\"" + this._BaudRate + "\" ";
            xml += RFCOMMReceiver.BUFFERSIZE_ATTRIBUTE + "=\"" + this._Buffer._Bytes.Length + "\" ";
            xml += RFCOMMReceiver.MAX_SR_ATTRIBUTE + "=\"" + this._MaximumSamplingRate + "\" ";
            xml += "/>";
            return xml;
        }
        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == RFCOMMReceiver.RECEIVER_ELEMENT))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {

                    if ((xAttribute.Name == RFCOMMReceiver.TYPE_ATTRIBUTE) && (xAttribute.Value != RFCOMMReceiver.RFCOMM_TYPE))
                        throw new Exception("XML Parsing error - RFCOMM receiver parsing a receiver of a different type " + xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.MACADDRESS_ATTRIBUTE)
                    {
                        this.address = xAttribute.Value;
                        this.address_bytes = new byte[MAC_SIZE];
                        for (int i = 0; (i < MAC_SIZE); i++)
                            this.address_bytes[i] = (byte)(System.Int32.Parse(address.Substring(i * 2, 2), System.Globalization.NumberStyles.AllowHexSpecifier) & 0xff);
                    }
                    else if (xAttribute.Name == RFCOMMReceiver.PIN_ATTRIBUTE)
                        this.pin = xAttribute.Value;
                    else if (xAttribute.Name == RFCOMMReceiver.PORT_NUMBER_ATTRIBUTE)
                        this._PortNumber = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.TSNIFF_ATTRIBUTE)
                        this._TSNIFF = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.PARITY_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "true")
                            this._Parity = true;
                        else
                            this._Parity = false;
                    }
                    else if (xAttribute.Name == RFCOMMReceiver.STOPBIT_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "true")
                            this._StopBit = true;
                        else
                            this._StopBit = false;
                    }
                    else if (xAttribute.Name == RFCOMMReceiver.BAUD_RATE_ATTRIBUTE)
                        this._BaudRate = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.BUFFERSIZE_ATTRIBUTE)
                        this._Buffer = new CircularBuffer(Convert.ToInt32(xAttribute.Value));//new byte[Convert.ToInt32(xAttribute.Value)];
                    else if (xAttribute.Name == RFCOMMReceiver.MAX_SR_ATTRIBUTE)
                        this._MaximumSamplingRate = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);

                }
            }
        }
        #endregion Serialization Functions
    }
}
