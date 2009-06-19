using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Utils;

namespace Wockets.Decoders.Accelerometers
{
    public sealed class WocketsDecoder: Decoder
    {
        #region Serialization Constants
        private const string WOCKETS_TYPE = "Wockets";
        #endregion Serialization Constants

        private const int BUFFER_SIZE = 600; 
        private bool headerSeen;
        
        public WocketsDecoder()
            : base(BUFFER_SIZE,WocketsAccelerationData.NUM_RAW_BYTES)
        {
            for (int i = 0; (i < this._Data.Length); i++)
                this._Data[i] = new WocketsAccelerationData();
            this.packetPosition = 0;
            this.headerSeen = false;
            this.type = DecoderTypes.Wockets;
        }

 
        public override int Decode(int sourceSensor,byte[] data, int length)       
        {
            int rawDataIndex = 0;   
            int numDecodedPackets=0;
               
            if (length != 0) // Have some data
            {
                while (rawDataIndex < length)
                {
                    if ((data[rawDataIndex] & 0x80) != 0) //grab the next 6 bytes
                    {
                        this.packetPosition = 0;
                        this.headerSeen = true;
                    }

                    if ((this.headerSeen == true) && (this.packetPosition < WocketsAccelerationData.NUM_RAW_BYTES))
                        this.packet[this.packetPosition] = data[rawDataIndex];

                    this.packetPosition++;
                    rawDataIndex++;


                    if ((this.packetPosition == WocketsAccelerationData.NUM_RAW_BYTES)) //a full packet was received
                    {

                        //if (this.head >= this._Data.Length)
                          //  throw new Exception("WocketsDecoder buffer too small " + this._Data.Length);

                        WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[this.head]);
                        datum.Reset();                        
                        //copy raw bytes
                        for (int i = 0; (i < WocketsAccelerationData.NUM_RAW_BYTES); i++)
                            datum.RawBytes[i] = this.packet[i];
                        datum.Type = SensorDataType.ACCEL;                       
                        //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                        datum.SensorID = (byte)sourceSensor;
                        datum.X = (short)(( ((short)(this.packet[0] & 0x03)) << 8) | (((short)(this.packet[1] & 0x7f)) << 1) | (((short)(this.packet[2] & 0x40)) >>6));
                        datum.Y = (short)((((short)(this.packet[2] & 0x3f)) << 4) | (((short)(this.packet[3] & 0x78)) >>3));
                        datum.Z = (short)((((short)(this.packet[3] & 0x07)) << 7) | ((short)(this.packet[4] & 0x7f)));
                        //Set time stamps
                        datum.UnixTimeStamp = WocketsTimer.GetUnixTime();
       
                        //if (IsValid(datum))
                         if (this.head>=(BUFFER_SIZE-1))
                             this.head=0;
                         else
                            this.head++;
                        numDecodedPackets++;
                        //decodedDataIndex= decodedDataIndex% BUFFER_SIZE;
                        this.packetPosition = 0;
                        this.headerSeen = false;
                    }
 
                }
            }
            //this._Size = decodedDataIndex;
            return numDecodedPackets;
        }



        /*public override bool IsValid(SensorData data)
        {

            return true;
        }*/


        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + WocketsDecoder.DECODER_ELEMENT + " ";
            xml += WocketsDecoder.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += WocketsDecoder.TYPE_ATTRIBUTE + "=\"" + WocketsDecoder.WOCKETS_TYPE + "\" ";
            xml += "/>";
            return xml;
        }

        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == WocketsDecoder.DECODER_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if ((xAttribute.Name == WocketsDecoder.TYPE_ATTRIBUTE) && (xAttribute.Value != WocketsDecoder.TYPE_ATTRIBUTE))
                        throw new Exception("XML Parsing error - wockets decoder parsing a decoder of a different type "+xAttribute.Value);
                    else if (xAttribute.Name == WocketsDecoder.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);  
                }
            }
        }
        #endregion Serialization Methods
    }
}
