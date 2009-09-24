using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Utils;

namespace Wockets.Decoders.Accelerometers
{
    public sealed class SparkfunDecoder: Decoder
    {
        #region Serialization Constants
        private const string SPARKFUN_TYPE = "Sparkfun";
        #endregion Serialization Constants

        private const int BUFFER_SIZE = 600; // should not exceed 4096 (Lower Level Buffer Size) / 5 (MITes Packet Size)
        private bool headerSeen;

        public SparkfunDecoder()
            : base(BUFFER_SIZE,SparkfunAccelerationData.NUM_RAW_BYTES)
        {
            for (int i = 0; (i < this._Data.Length); i++)
                this._Data[i] = new SparkfunAccelerationData();
            this.packetPosition = 0;
            this.headerSeen = false;
            this.type = DecoderTypes.Sparkfun;
        }

        public override int Decode(int sourceSensor, CircularBuffer data,int start,int end)
        {
            return 0;
        }
        public override int Decode(int sourceSensor, byte[] data, int length)
        {
            int rawDataIndex = 0;
            int decodedDataIndex = 0;      


            if (length != 0) // Have some data
            {
                while (rawDataIndex < length)
                {
                    if ((data[rawDataIndex]) == '#') //grab the next 6 bytes
                    {
                        this.packetPosition = 0;
                        this.headerSeen = true;
                    }

                    if ((this.headerSeen == true) && (this.packetPosition < SparkfunAccelerationData.NUM_RAW_BYTES))
                       this.packet[this.packetPosition] = data[rawDataIndex];

                   this.packetPosition++;                    
                    rawDataIndex++;
                    if ((this.packetPosition == SparkfunAccelerationData.NUM_RAW_BYTES) && (packet[SparkfunAccelerationData.NUM_RAW_BYTES - 1] == '$')) //a full packet was received
                    {
                        //DecodeSparkfunFrame(someData[dataIndex], packet3);

                        if (decodedDataIndex >= this._Data.Length)
                            throw new Exception("SparkfunDecoder buffer too small " + this._Data.Length);

                        // completely read a whole packet                       
                        SparkfunAccelerationData datum = ((SparkfunAccelerationData)this._Data[decodedDataIndex]);
                        //Reset the data element
                        datum.Reset();
                        //copy raw bytes
                        for (int i = 0; (i < SparkfunAccelerationData.NUM_RAW_BYTES); i++)
                            datum.RawBytes[i] = this.packet[i];

                        //decode sparkfun packet
                        datum.Type = SensorDataType.ACCEL;
                        datum.SensorID = (byte) sourceSensor;
                        datum.X = (short)((((short)this.packet[4]) << 8) | ((short)this.packet[5]));
                        datum.Y = (short)((((short)this.packet[6]) << 8) | ((short)this.packet[7]));
                        datum.Z = (short)((((short)this.packet[8]) << 8) | ((short)this.packet[9]));                        

                        //Set time stamps
                        datum.UnixTimeStamp = WocketsTimer.GetUnixTime();
                        //if (IsValid(datum))
                        decodedDataIndex++;   
                        this.packetPosition = 0;
                        this.headerSeen = false;
               
                    }
                }
            }
            this._Size = decodedDataIndex;
            return decodedDataIndex;
        }

       /* public override bool IsValid(SensorData data)
        {

            return true;
        }*/

        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + SparkfunDecoder.DECODER_ELEMENT + " ";
            xml += SparkfunDecoder.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += SparkfunDecoder.TYPE_ATTRIBUTE + "=\"" + SparkfunDecoder.SPARKFUN_TYPE + "\" ";
            xml += "/>";
            return xml;
        }

        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == SparkfunDecoder.DECODER_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if ((xAttribute.Name == SparkfunDecoder.TYPE_ATTRIBUTE) && (xAttribute.Value != SparkfunDecoder.TYPE_ATTRIBUTE))
                        throw new Exception("XML Parsing error - Sparkfun decoder parsing a decoder of a different type " + xAttribute.Value);
                    else if (xAttribute.Name == SparkfunDecoder.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);  
                }
            }
        }
        #endregion Serialization Methods
    }
}
