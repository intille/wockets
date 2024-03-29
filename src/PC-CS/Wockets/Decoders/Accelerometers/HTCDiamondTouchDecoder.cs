using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Utils;

namespace Wockets.Decoders.Accelerometers
{
    public sealed class HTCDiamondTouchDecoder : Decoder
    {
        #region Serialization Constants
        private const string HTCDIAMOND_TYPE = "HTCDiamondTouch";
        private const int HTCDIAMOND_CHANNEL = 83;
        #endregion Serialization Constants

        private const int BUFFER_SIZE = 512; // should not exceed 4096 (Lower Level Buffer Size) / 6 (HTC Packet Size)
        private bool headerSeen;



        public HTCDiamondTouchDecoder()
            : base(BUFFER_SIZE, HTCDiamondTouchAccelerationData.NUM_RAW_BYTES)
        {     
           
            this.packetPosition = 0;
            this.headerSeen = false;
            this.type = DecoderTypes.HTCDiamondTouch;
        }

        public override bool Initialize()
        {
            base.Initialize();
            if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)
            {
                for (int i = 0; (i < this._Data.Length); i++)
                    this._Data[i] = new HTCDiamondTouchAccelerationData();
            }
            return true;
        }
        /*
        public override bool IsValid(SensorData data)
        {
            //Check for valid HTC Channels
            if (data.Channel != HTCDIAMOND_CHANNEL)
                return false;
            return true;
        }
         */

        public override int Decode(int sourceSensor, CircularBuffer data, int start,int end)
        {
            int rawDataIndex = start;
            int numDecodedPackets = 0;

            //count number of packets to decode
            int dataLength = end - start; //((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail - currentReceiver._Head;
            if (dataLength < 0)
                dataLength = data._Bytes.Length - start+ end;//((RFCOMMReceiver)currentReceiver).bluetoothStream._Buffer.Length - currentReceiver._Head + ((RFCOMMReceiver)currentReceiver).bluetoothStream._Tail;
            int maxDecodedPackets = dataLength / HTCDiamondTouchAccelerationData.NUM_RAW_BYTES;

            while ((maxDecodedPackets > 0) && (rawDataIndex != end))
            {
                //lock (data._Bytes)
                //{
                    int firstByte = rawDataIndex;
                    int lastByte = (rawDataIndex + HTCDiamondTouchAccelerationData.NUM_RAW_BYTES - 1) % data._Bytes.Length;


                    if ((data._Bytes[firstByte] == 0xff) && ((data._Bytes[lastByte] == 0xff)))
                    {
                        HTCDiamondTouchAccelerationData datum = ((HTCDiamondTouchAccelerationData)this._Data[this.head]);
                        datum.Reset();
                        //copy raw bytes
                        for (int i = 0; (i < HTCDiamondTouchAccelerationData.NUM_RAW_BYTES); i++)
                        {
                            datum.RawBytes[i] = data._Bytes[rawDataIndex];
                            rawDataIndex = (rawDataIndex + 1) % data._Bytes.Length;
                        }
                        datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                        datum._SensorID = (byte)sourceSensor;
                        datum._X = (short)(BitConverter.ToInt16(datum.RawBytes, 1) + 1024);
                        datum._Y = (short)(BitConverter.ToInt16(datum.RawBytes, 3) + 1024);
                        datum._Z = (short)(BitConverter.ToInt16(datum.RawBytes, 5) + 1024);
                        datum.UnixTimeStamp = WocketsTimer.GetUnixTime();

                        if (this.head >= (BUFFER_SIZE - 1))
                            this.head = 0;
                        else
                            this.head++;

                        numDecodedPackets++;
                        data._Head = (data._Head + HTCDiamondTouchAccelerationData.NUM_RAW_BYTES) % data._Bytes.Length;

                        if (numDecodedPackets == maxDecodedPackets)
                            break;
                    }
                    else
                        break;
                //}
            }
           
            return numDecodedPackets;
        }
        public override int Decode(int sensorID, byte[] data, int length)
        {
            int rawDataIndex = 0;
            int numDecodedPackets = 0;


            if ((length != 0) && (data[0] == 0xff) && (data[15] == 0xff) && (length == HTCDiamondTouchAccelerationData.NUM_RAW_BYTES)) // Have some data
            {


               // if (decodedDataIndex >= this._Data.Length)
                //    throw new Exception("HTC Diamond Touch buffer too small " + this._Data.Length);

                HTCDiamondTouchAccelerationData datum = ((HTCDiamondTouchAccelerationData)this._Data[this.head]);
                datum.Reset();
                //copy raw bytes
                for (int i = 0; (i < HTCDiamondTouchAccelerationData.NUM_RAW_BYTES); i++)
                    datum.RawBytes[i] = data[i];
                datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                datum._SensorID = (byte)sensorID;
                datum._X = (short)(BitConverter.ToInt16(data, 1) + 1024);
                datum._Y = (short)(BitConverter.ToInt16(data, 3) + 1024);
                datum._Z = (short)(BitConverter.ToInt16(data, 5) + 1024);
                //Set time stamps
                datum.UnixTimeStamp = WocketsTimer.GetUnixTime();

                //if (IsValid(datum))
                if (this.head >= (BUFFER_SIZE - 1))
                    this.head = 0;
                else
                    this.head++;

                numDecodedPackets++;
                this.headerSeen = false;

            }

            return numDecodedPackets;
        }

        private byte[] b6 = new byte[6];
        private byte[] b = new byte[1];
        private double lastUnixTime = 0;
        byte[] header = new byte[1];
        byte[] pdu = new byte[16];

        public override void Load(ByteReader br)
        {
            #region Read Timestamp
            if (!(br.ReadByte(b)))
                throw new Exception("Error: reading first byte in PLFormat file");

            //read a complete timestamp
            if (b[0] == ((int)255))
            {
                if (!(br.ReadBytes(b6)))
                    throw new Exception("Error: reading full timestamp in PLFormat file");

                lastUnixTime = WocketsTimer.DecodeUnixTimeCodeBytesFixed(b6);
            }
            else //read a differential timestamp          
                lastUnixTime += (int)b[0];

            #endregion Read Timestamp

            DateTime dt = new DateTime();
            WocketsTimer.GetDateTime((long)lastUnixTime, out dt);

            if (!br.ReadByte(header))
                throw new Exception("Error: reading data in PLFormat file");
            pdu[0] = header[0];


            if (!(br.ReadBytes(pdu, 1, 16)))
                throw new Exception("Error: reading data in PLFormat file");


            int lastDecodedIndex = 0;
            //Successfully decoded a packet
            if (this.Decode(this._ID, pdu, 16) == 1)
            {
                if (this._Head == 0)
                    lastDecodedIndex = this._Data.Length - 1;
                else
                    lastDecodedIndex = this._Head - 1;
                this._Data[lastDecodedIndex].UnixTimeStamp = lastUnixTime;
                return;
            }
            else
                throw new Exception("Failed to decode data");
        }
        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + HTCDiamondTouchDecoder.DECODER_ELEMENT + " ";
            xml += HTCDiamondTouchDecoder.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += HTCDiamondTouchDecoder.TYPE_ATTRIBUTE + "=\"" + HTCDiamondTouchDecoder.HTCDIAMOND_TYPE + "\" ";
            xml += "/>";
            return xml;
        }

        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == HTCDiamondTouchDecoder.DECODER_ELEMENT))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if ((xAttribute.Name == HTCDiamondTouchDecoder.TYPE_ATTRIBUTE) && (xAttribute.Value != HTCDiamondTouchDecoder.HTCDIAMOND_TYPE))
                        throw new Exception("XML Parsing error - HTC Diamond decoder parsing a decoder of a different type " + xAttribute.Value);
                    else if (xAttribute.Name == HTCDiamondTouchDecoder.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);
                }
            }
        }
        #endregion Serialization Methods
    }
}
