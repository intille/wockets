using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Utils;

namespace Wockets.Decoders.Accelerometers
{
    public sealed class MITesDecoder: Decoder
    {
        #region Serialization Constants
        private const string MITES_TYPE = "MITes";
        #endregion Serialization Constants
            
        private const int BUFFER_SIZE = 600; // should not exceed 4096 (Lower Level Buffer Size) / 5 (MITes Packet Size)
        private const int NO_HEADER_SEEN = -9;
        private const int FIRST_HEADER_SEEN = -10;
        private const int PACKET_MARKER = 68;
        private int v = 0;
        private int lV = 0;

        public MITesDecoder()
            : base(BUFFER_SIZE,MITesAccelerationData.NUM_RAW_BYTES)
        {
            for (int i = 0; (i < this._Data.Length); i++)
                this._Data[i] = new MITesAccelerationData();
            this.packetPosition=NO_HEADER_SEEN;
            this.type = DecoderTypes.MITes;
        }



        /*
        public override bool IsValid(SensorData data)
        {
            //Check for valid MITes channels
            if ((data.Channel != 0) && (data.Channel != 1) && (data.Channel != 4) && (data.Channel != 7)
                && (data.Channel != 8) && (data.Channel != 11) && (data.Channel != 14) && (data.Channel != 17))
                return false;

            return true;
        }*/

        public override int Decode(int sourceSensor, CircularBuffer data,int start,int end)
        {
            return 0;
        }
        //exception thrown only when there is an overflow
        public override int Decode(int sensorID, byte[] data, int length)
        {
            int rawDataIndex = 0;
            int decodedDataIndex = 0;
         
            if (length != 0) // Have some data
            {
                while (rawDataIndex < length)
                {
                    v = data[rawDataIndex] & 0xff;

                    // First check if got a reset and start of packet
                    if ((this.packetPosition == NO_HEADER_SEEN) && (v == PACKET_MARKER))
                        this.packetPosition = FIRST_HEADER_SEEN;                    
                    // Any two markers in a row is *always* a packet. This will occasionally cause an error. 
                    else if ((v == PACKET_MARKER) && (lV == PACKET_MARKER))
                        this.packetPosition = 0;                                        
                    else if (this.packetPosition >= 0) // Must have seen header
                    {
                        this.packet[this.packetPosition] = data[rawDataIndex];
                        this.packetPosition++;

                        if (this.packetPosition == MITesAccelerationData.NUM_RAW_BYTES)
                        {
                            if (decodedDataIndex >= this._Data.Length)
                                throw new Exception("MITesDecoder buffer too small " + this._Data.Length);
                            
                            // completely read a whole packet                       
                            MITesAccelerationData datum = ((MITesAccelerationData)this._Data[decodedDataIndex]);
                            //Reset the data element
                            datum.Reset();
                            //copy raw bytes
                            for (int i = 0; (i < MITesAccelerationData.NUM_RAW_BYTES); i++)
                                datum.RawBytes[i] = this.packet[i];

                            //Decode the MITes axes data
                            datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                            datum._SensorID = (byte) sensorID;
                            datum.X = (short)(this.packet[1] | ((this.packet[4] & 0xC0) << 2));
                            datum.Y = (short)(this.packet[2] | ((this.packet[4] & 0x30) << 4));
                            datum.Z = (short)(this.packet[3] | ((this.packet[4] & 0x0C) << 6));

                            //Set time stamps
                            datum.UnixTimeStamp = WocketsTimer.GetUnixTime();
                            //if (IsValid(datum))                            
                             decodedDataIndex++;                            
               
                            //Reset for a new packet
                            this.packetPosition = 0;                             
                        }

                    }
                    else
                    {
                        if (v != PACKET_MARKER)
                            packetPosition = NO_HEADER_SEEN;
                        else
                            packetPosition = FIRST_HEADER_SEEN;
 
                    }

                    lV = v;
                    rawDataIndex++;
                }

            }
            this._Size = decodedDataIndex;
            return decodedDataIndex;
        }

        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + MITesDecoder.DECODER_ELEMENT + " ";
            xml += MITesDecoder.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += MITesDecoder.TYPE_ATTRIBUTE + "=\"" + MITesDecoder.MITES_TYPE + "\" ";
            xml += "/>";
            return xml;
        }

        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == MITesDecoder.DECODER_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if ((xAttribute.Name == MITesDecoder.TYPE_ATTRIBUTE) && (xAttribute.Value != MITesDecoder.MITES_TYPE))
                        throw new Exception("XML Parsing error - mites decoder parsing a decoder of a different type " + xAttribute.Value);
                    else if (xAttribute.Name == MITesDecoder.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);  
                }
            }
        }
        #endregion Serialization Methods
    }
}
