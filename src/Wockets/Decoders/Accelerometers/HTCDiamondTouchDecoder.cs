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
        private const string HTCDIAMOND_TYPE = "HTCDiamond";
        private const int HTCDIAMOND_CHANNEL = 83;
        #endregion Serialization Constants

        private const int BUFFER_SIZE = 200; // should not exceed 4096 (Lower Level Buffer Size) / 6 (HTC Packet Size)
        private bool headerSeen;



        public HTCDiamondTouchDecoder()
            : base(BUFFER_SIZE, HTCDiamondTouchAccelerationData.NUM_RAW_BYTES)
        {

            for (int i = 0; (i < this._Data.Length); i++)
                this._Data[i] = new HTCDiamondTouchAccelerationData();
            this.packetPosition = 0;
            this.headerSeen = false;
            this.type = DecoderTypes.HTCDiamondTouch;
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

        public override int Decode(int sourceSensor, byte[] data, int head, int tail)
        {
            return 0;
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
                datum.Type = SensorDataType.ACCEL;
                datum.SensorID = (byte)sensorID;
                datum.X = (short)(BitConverter.ToInt16(data, 1) + 1024);
                datum.Y = (short)(BitConverter.ToInt16(data, 3) + 1024);
                datum.Z = (short)(BitConverter.ToInt16(data, 5) + 1024);
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

            if ((xNode.Name == HTCDiamondTouchDecoder.DECODER_ELEMENT) && (xNode.HasChildNodes))
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
