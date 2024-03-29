using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Threading;
using Wockets.Utils;
using System.IO.Ports;
//using HousenCS.SerialIO;


namespace Wockets.Receivers
{
    public sealed class StandardCOMReceiver:SerialReceiver
    {
        #region Serialization Constants
        private const string StandardCOM_TYPE = "StandardCOM";
        #endregion Serialization Constants

        //Standard COM Configuration
        private const bool USE_PARITY = false;
        private const bool USE_STOP_BIT = true;
        private const int BAUD_RATE=57600;
        private const int BUFFER_SIZE = 4096;
        private const int SEND_BUFFER_SIZE = 256;
        private const int MAXIMUM_SAMPLING_RATE = 180;

        //Standard COM Specific Objects
        private int portNumber;
        private SerialPort spc;

        public StandardCOMReceiver()
            : base(BUFFER_SIZE)
        {
            this.type = ReceiverTypes.StandardCOM;
        }


 


        public override bool Initialize()
        {
            bool isValid = true;

            SerialPort spc = new SerialPort();
            Thread.Sleep(1000);
            spc.BaudRate=BAUD_RATE;
            spc.PortName = "COM" + this.portNumber;
            if (this._Parity)
                spc.Parity = Parity.Odd;
            else
                spc.Parity = Parity.None;

            if (this._StopBit)
                spc.StopBits = StopBits.One;
            else
                spc.StopBits = StopBits.None;

            try
            {
                spc.Open();
            }
            catch (Exception)
            {
                isValid = false;
            }

        

            if (isValid)
            {
                isValid = false;
                byte[] someData = new byte[4000];
                int startTime = Environment.TickCount;
                // Loop for 1 second and wait for a DD 
                while ((Environment.TickCount - startTime) < 1000)
                {
                    int j = spc.Read(someData,0,someData.Length);
                    //Console.WriteLine ("Data: " + someData.Length);
                    if (j > 1)
                        for (int i = 0; i < j - 1; i++)
                            if ((someData[i] == (int)68) &&
                                (someData[i + 1] == (int)68))
                                isValid = true;                    
                    Thread.Sleep(100);
                }
            }

            if (isValid)
            {
                this.spc = spc;
                //this._Running = true;
                this._Status = ReceiverStatus.Connected;
            }
            return isValid;
        }

        public override void Update()
        {
        }

        
        public override bool Dispose()
        {
            try
            {
                spc.Close();
                //this._Running = false;
                this._Status = ReceiverStatus.Disposed;
                return true;
            }
            catch(Exception)
            {
                return false;
            }
        }

        public override void Write(byte[] data)
        {    
        }
    
        //Optimization
        //Get rid of the buffer created with spc and used in port_DataReceived()
        //Get rid of the decoding happening at initialization
        //Code is not guruanteed to be thread-safe
        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + StandardCOMReceiver.RECEIVER_ELEMENT + " ";
            xml += StandardCOMReceiver.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += StandardCOMReceiver.TYPE_ATTRIBUTE + "=\"" + StandardCOMReceiver.StandardCOM_TYPE + "\" ";
            xml += StandardCOMReceiver.PORT_NUMBER_ATTRIBUTE+ "=\"" + this._PortNumber + "\" ";
            xml += StandardCOMReceiver.PARITY_ATTRIBUTE + "=\"" + this._Parity + "\" ";
            xml += StandardCOMReceiver.STOPBIT_ATTRIBUTE + "=\"" + this._StopBit + "\" ";
            xml += StandardCOMReceiver.BAUD_RATE_ATTRIBUTE + "=\"" + this._BaudRate + "\" ";
            xml += StandardCOMReceiver.BUFFERSIZE_ATTRIBUTE + "=\"" + this._Buffer._Bytes.Length + "\" ";
            xml += StandardCOMReceiver.MAX_SR_ATTRIBUTE + "=\"" + this._MaximumSamplingRate + "\" ";
            xml += "/>";
            return xml;
        }

        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == StandardCOMReceiver.RECEIVER_ELEMENT) )
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {

                    if ((xAttribute.Name == StandardCOMReceiver.TYPE_ATTRIBUTE) && (xAttribute.Value != StandardCOMReceiver.StandardCOM_TYPE))
                        throw new Exception("XML Parsing error - Standard COM receiver parsing a receiver of a different type " + xAttribute.Value);
                    else if (xAttribute.Name == StandardCOMReceiver.PORT_NUMBER_ATTRIBUTE)
                        this._PortNumber = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == StandardCOMReceiver.PARITY_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "true")
                            this._Parity = true;
                        else
                            this._Parity = false;
                    }
                    else if (xAttribute.Name == StandardCOMReceiver.STOPBIT_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "true")
                            this._StopBit = true;
                        else
                            this._StopBit = false;
                    }
                    else if (xAttribute.Name == StandardCOMReceiver.BAUD_RATE_ATTRIBUTE)
                        this._BaudRate = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == StandardCOMReceiver.BUFFERSIZE_ATTRIBUTE)
                        this._Buffer = new CircularBuffer(Convert.ToInt32(xAttribute.Value));//new byte[Convert.ToInt32(xAttribute.Value)];
                    else if (xAttribute.Name == StandardCOMReceiver.MAX_SR_ATTRIBUTE)
                        this._MaximumSamplingRate = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == StandardCOMReceiver.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);

                }
            }
        }
        #endregion Serialization Methods
    }
}
