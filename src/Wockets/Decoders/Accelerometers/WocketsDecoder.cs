
using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Data.Commands;
using Wockets.Utils;

namespace Wockets.Decoders.Accelerometers
{
    public sealed class WocketsDecoder: Decoder
    {
        #region Serialization Constants
        private const string WOCKETS_TYPE = "Wockets";
        #endregion Serialization Constants

        private const int BUFFER_SIZE = 1200; 
        private bool headerSeen;
        private int bytesToRead = 0;
        private SensorDataType packetType;
        private double lastTimestamp;

        public WocketsDecoder()
            : base(BUFFER_SIZE, (WocketsAccelerationData.NUM_RAW_BYTES > Wockets.Data.Responses.Response.MAX_RAW_BYTES) ? WocketsAccelerationData.NUM_RAW_BYTES : Wockets.Data.Responses.Response.MAX_RAW_BYTES)
        {
            for (int i = 0; (i < this._Data.Length); i++)
                this._Data[i] = new WocketsAccelerationData();
            this.packetPosition = 0;
            this.headerSeen = false;
            this.type = DecoderTypes.Wockets;
        }


        public override int Decode(int sourceSensor, byte[] data, int head, int tail)
        {

            int rawDataIndex = head;
            int numDecodedPackets = 0;
            int bufferHead = this.head;


            while (rawDataIndex !=tail)
            {
                if (this.cmd && data[rawDataIndex] == ((byte)'C'))
                {
                    if (rawDataIndex + 1 != tail && data[rawDataIndex + 1] == ((byte)'M'))
                    {
                        if (rawDataIndex + 2 != tail && data[rawDataIndex + 2] == ((byte)'D'))
                            this.cmd = false;
                    }
                }

                if ((data[rawDataIndex] & 0x80) != 0) //grab the next 6 bytes
                {
                    this.packetPosition = 0;
                    this.headerSeen = true;
                    int headerByte = ((byte)(((byte)data[rawDataIndex]) << 1)) >> 6;
                    if (headerByte == 0)
                    {
                        bytesToRead = WocketsAccelerationData.NUM_RAW_BYTES;
                        packetType = SensorDataType.ACCEL;
                    }
                    else if (headerByte == 2)
                    {

                        int opcode = (((byte)data[rawDataIndex]) & 0x1f);
                        if (opcode == 0)
                        {
                            bytesToRead = 3;
                            packetType = SensorDataType.BATTERYLEVEL;
                        }
                        else if (opcode == 0x04)
                        {
                            bytesToRead = 10;
                            packetType = SensorDataType.CALIBRATION_VALUES;
                        }


                    }
                }

                if ((this.headerSeen == true) && (this.packetPosition < bytesToRead))
                    this.packet[this.packetPosition] = data[rawDataIndex];
                    
                this.packetPosition++;
                rawDataIndex=(rawDataIndex+1)%data.Length;


                if ((this.packetPosition == bytesToRead)) //a full packet was received
                {
                    if (packetType == SensorDataType.ACCEL)
                    {

                        WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[bufferHead]);
                        datum.Reset();
                        datum.UnixTimeStamp = WocketsTimer.GetUnixTime();
                        //copy raw bytes
                        for (int i = 0; (i < bytesToRead); i++)
                            datum.RawBytes[i] = this.packet[i];
                        datum.Type = SensorDataType.ACCEL;
                        //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                        datum.SensorID = (byte)sourceSensor;
                        datum.X = (short)((((short)(this.packet[0] & 0x03)) << 8) | (((short)(this.packet[1] & 0x7f)) << 1) | (((short)(this.packet[2] & 0x40)) >> 6));
                        datum.Y = (short)((((short)(this.packet[2] & 0x3f)) << 4) | (((short)(this.packet[3] & 0x78)) >> 3));
                        datum.Z = (short)((((short)(this.packet[3] & 0x07)) << 7) | ((short)(this.packet[4] & 0x7f)));
                        //Set time stamps                       
                        datum._PeggyBacked = ((this.packet[0] & 0x1c) > 0);
                        if (datum._PeggyBacked)
                            datum._PeggyBacked = true;

                        //if (IsValid(datum))
                        if (bufferHead >= (BUFFER_SIZE - 1))
                            bufferHead = 0;
                        else
                            bufferHead++;
                        numDecodedPackets++;

                        


                        this.packetPosition = 0;
                        this.headerSeen = false;

                        //if (numDecodedPackets > 45)
                        //    break;
                    }
                    else if (packetType == SensorDataType.BATTERYLEVEL)
                    {

                        BatteryResponse br = new BatteryResponse(this._ID);
                        for (int i = 0; (i < bytesToRead); i++)
                            br.RawBytes[i] = this.packet[i];
                        br.BatteryLevel = (((int)this.packet[1]) << 3) | ((this.packet[2] >> 4) & 0x07);
                        Response.ResponseArgs e = new Response.ResponseArgs();
                        e._Response = br;
                        FireEvent(e);

                    }
                    else if (packetType == SensorDataType.CALIBRATION_VALUES)
                    {
         
                        int x1g = ((this.packet[1] & 0x7f) << 3)| ((this.packet[2]&0x70)>>4);
                        int x1ng= ((this.packet[2]&0x0f)<<6) |((this.packet[3]&0x7e)>>1);
                        int y1g=((this.packet[3]&0x01)<<9) |((this.packet[4]&0x7f)<<2)|((this.packet[5]&0x60)>>5);
                        int y1ng=((this.packet[5]&0x1f)<<5)|((this.packet[6]&0x7c)>>2);
                        int z1g=((this.packet[6]&0x03)<<8) | ((this.packet[7]&0x7f)<<1) |((this.packet[8]&0x40)>>6);
                        int z1ng= ((this.packet[8]&0x3f)<<4) | ((this.packet[9]&0x78)>>3);                        
                    }

                }

            }

            //Fix timestamps
 /*
            double currentTimestamp = lasttimestamp - numDecodedPackets * samplespacing;
            
            if (currentTimestamp < this.lastTimestamp) //no problem
            {
                samplespacing = (lasttimestamp - this.lastTimestamp) / numDecodedPackets;
                currentTimestamp = samplespacing + this.lastTimestamp;
            }
            int currentHead = this.head;
            for (int i = 0; (i < numDecodedPackets); i++)
            {
                ((WocketsAccelerationData)this._Data[currentHead]).UnixTimeStamp = currentTimestamp;
                currentTimestamp += samplespacing;

                if (currentHead >= (BUFFER_SIZE - 1))
                    currentHead = 0;
                else
                    currentHead++;
            }

            this.lastTimestamp = currentTimestamp;
  */
            this.head = bufferHead;
            //this._Size = decodedDataIndex;
            return numDecodedPackets;
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
                        int headerByte=((byte)(((byte)data[rawDataIndex])<<1))>>6;
                        if (headerByte==0){
                            bytesToRead=WocketsAccelerationData.NUM_RAW_BYTES;
                            packetType=SensorDataType.ACCEL;
                        }
                        else if (headerByte==2){                         
                            bytesToRead=3;  
                            packetType=SensorDataType.BATTERYLEVEL;
                        }
                    }
                    
                     if ((this.headerSeen == true) && (this.packetPosition < bytesToRead))
                         this.packet[this.packetPosition] = data[rawDataIndex];

                    this.packetPosition++;
                    rawDataIndex++;


                    if ((this.packetPosition == bytesToRead)) //a full packet was received
                    {
                        if (packetType == SensorDataType.ACCEL)
                        {

                            WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[this.head]);
                            datum.Reset();
                            //copy raw bytes
                            for (int i = 0; (i < bytesToRead); i++)
                                datum.RawBytes[i] = this.packet[i];
                            datum.Type = SensorDataType.ACCEL;
                            //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                            datum.SensorID = (byte)sourceSensor;
                            datum.X = (short)((((short)(this.packet[0] & 0x03)) << 8) | (((short)(this.packet[1] & 0x7f)) << 1) | (((short)(this.packet[2] & 0x40)) >> 6));
                            datum.Y = (short)((((short)(this.packet[2] & 0x3f)) << 4) | (((short)(this.packet[3] & 0x78)) >> 3));
                            datum.Z = (short)((((short)(this.packet[3] & 0x07)) << 7) | ((short)(this.packet[4] & 0x7f)));
                            //Set time stamps
                            datum.UnixTimeStamp = WocketsTimer.GetUnixTime();

                            //if (IsValid(datum))
                            if (this.head >= (BUFFER_SIZE - 1))
                                this.head = 0;
                            else
                                this.head++;
                            numDecodedPackets++;

                            this.packetPosition = 0;
                            this.headerSeen = false;
                        }
                        else if (packetType == SensorDataType.BATTERYLEVEL)
                        {
                            
                          /*  BatteryResponse br = new BatteryResponse();
                            for (int i = 0; (i < bytesToRead); i++)
                                br.RawBytes[i] = this.packet[i];
                            br.BatteryLevel = (((int)this.packet[1]) << 3) | ((this.packet[2] >> 4) & 0x07);
                            this._Response[0] = br;*/
                        
                       }
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
