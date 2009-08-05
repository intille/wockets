using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.Xml;
using System.IO;
using System.Net.Sockets;
using System.IO.Ports;
using HousenCS.SerialIO;
using System.Runtime.InteropServices;
using System.Threading;
using Wockets.Utils;
using System.Net;
using Microsoft.Win32;
using Wockets.Utils.network;
using Wockets.Utils.network.Bluetooth;
using Wockets.Utils.network.Bluetooth.Microsoft;
using Wockets.Utils.network.Bluetooth.Widcomm;

#if (PocketPC)
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
using InTheHand.Net.Ports;
#endif

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
        private const int BUFFER_SIZE = 4096;
        private const int PORT_NUMBER = 9;
        private const int MAXIMUM_SAMPLING_RATE = 70;

        //RFCOMM Specific Objects
#if (PocketPC)
        //private BluetoothStream bluetoothStream;       

        private BluetoothStream bluetoothStream;
#endif
        private const int MAC_SIZE = 6;
        private string address;
        private byte[] address_bytes;
        private string pin;
        private int sniffTime = 0;
        private bool sniffMode;
        private int aliveTimer = 0;

        public RFCOMMReceiver():base(BUFFER_SIZE)
        {
            this.type = ReceiverTypes.RFCOMM;

            //initialize the stack

        }
        public override int _Tail
        {
            get
            {
                return this.bluetoothStream._Tail;
            }
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
                /*
                if (this.bluetoothStream._Status == BluetoothStatus.Disconnected)
                    throw new Exception("Wocket " + this.address + " disconnected");
                else if (this.bluetoothStream._Status == BluetoothStatus.Disposed)
                {
                    this.bluetoothStream._Status = BluetoothStatus.Reconnecting;
                    reconnectionThread = new Thread(new ThreadStart(this.Reconnect));
                    reconnectionThread.Start();                    
                }
                */
               
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
                if ((this.bluetoothStream != null) && (this.bluetoothStream._Status == BluetoothStatus.Disconnected))
                {
                    NetworkStacks._BluetoothStack.Disconnect(this.bluetoothStream._HexAddress);
                    this.bluetoothStream = null;
                    this.ndisc += 1;
                    this.disconCount = 1;
                    this.lastTime = DateTime.Now.Ticks;
                    Logger.Warn("Sensor " + this._ID + " has disconnected.");
                }

                if ((this.bluetoothStream == null) && (this.status != ReceiverStatus.Reconnecting))
                {
                    this.status = ReceiverStatus.Reconnecting;
                    reconnectionThread = new Thread(new ThreadStart(this.Reconnect));
                    reconnectionThread.Start();
                }

                if ((this.status != ReceiverStatus.Connected) && (this.bluetoothStream != null) && (this.bluetoothStream._Status == BluetoothStatus.Connected))
                {
                    if (this.status == ReceiverStatus.Reconnecting)
                    {
                        reconnectionThread.Join();
                        reconnectionThread.Abort();
                        reconnectionThread = null;
                    }
                    this.status = ReceiverStatus.Connected;
                    Logger.Warn("Sensor " + this._ID + " has connected.");
                    this.disconCount = 0;
                    if (this.lastTime!=0)
                        this.disconTime += (int)((DateTime.Now.Ticks - this.lastTime) / 10000000);
                }

                if (aliveTimer >= 100)
                {
                    this.Send(Data.Commands.RFCOMMCommand.Alive());
                    aliveTimer = 0;
                }
                aliveTimer++;
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


        [DllImport("coredll.dll", SetLastError = true)]
        public static extern int CeSetThreadQuantum(IntPtr handle,short msec);

        public void Send(Data.Commands.RFCOMMCommand cmd)
        {
            this.bluetoothStream.Send(cmd.CMD);
        }

        private void Reconnect()
        {
            //CeSetThreadQuantum(new IntPtr(reconnectionThread.ManagedThreadId), 20);
            while ((this.bluetoothStream==null)|| (this.bluetoothStream._Status!= BluetoothStatus.Connected))//(this._Status == ReceiverStatus.Reconnecting)
            {
                try
                {
                    if (this.Initialize())
                    {
                        //this.status = ReceiverStatus.Connected;
                        Wockets.Utils.Logger.Warn("Receiver " + this._ID + " has reconnected.");                    
                    }
                }
                catch (Exception e)
                {
                }
                Thread.Sleep(500);
            }
        }

        public override bool Initialize()
        {

            try
            {
                this.bluetoothStream=NetworkStacks._BluetoothStack.Connect(this._Buffer, this.address_bytes, this.pin);
                if (this.bluetoothStream == null)
                    return false;       
                return true;
            }
            catch (Exception e)
            {
                return false;
            }
        }


        public override bool Dispose()
        {
            try
            {
#if (PocketPC)
                //this._Running = false;
                this._Status = ReceiverStatus.Disconnected;
                //NetworkStacks._BluetoothStack.Disconnect(this.address_bytes);
                //this.bluetoothStream._Status = BluetoothStatus.Disposed;
#endif
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
            xml += RFCOMMReceiver.BUFFERSIZE_ATTRIBUTE + "=\"" + this._Buffer.Length + "\" ";
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
                        this._Buffer = new byte[Convert.ToInt32(xAttribute.Value)];
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
