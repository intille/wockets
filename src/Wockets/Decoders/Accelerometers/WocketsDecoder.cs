using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Data.Commands;
using Wockets.Data.Responses;
using Wockets.Utils;
using Wockets.Exceptions;

#if (PocketPC)
using Wockets.Utils.IPC.MMF;
#endif

namespace Wockets.Decoders.Accelerometers
{
    public sealed class WocketsDecoder: Decoder
    {
        #region Serialization Constants
        private const string WOCKETS_TYPE = "Wockets";
        #endregion Serialization Constants

        public const int BUFFER_SIZE = 8192; 
        private bool headerSeen;
        private double timestamp = 0;
        private int bytesToRead = 0;
        private SensorDataType packetType;
        private double lastTimestamp;
        public int _ExpectedPacketCount = 0;
        public double _ReferenceTime = 0;

        public WocketsDecoder()
            : base(BUFFER_SIZE, (WocketsAccelerationData.NUM_RAW_BYTES > Wockets.Data.Responses.Response.MAX_RAW_BYTES) ? WocketsAccelerationData.NUM_RAW_BYTES : Wockets.Data.Responses.Response.MAX_RAW_BYTES)
        {
      
            this.packetPosition = 0;
            this.headerSeen = false;
            this.type = DecoderTypes.Wockets;
        }


        public override bool Initialize()
        {
            base.Initialize();
            if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)
            {
                for (int i = 0; (i < this._Data.Length); i++)
                    this._Data[i] = new WocketsAccelerationData();
            }
            return true;
        }
        public override int Decode(int sourceSensor, CircularBuffer data,int start,int end)
        {


            int rawDataIndex = start;
            int numDecodedPackets = 0;
            //int bufferHead = this.head;


            while (rawDataIndex != end)
            {
                if (this._Mode == DecoderModes.Command)
                {
                    int plen=this.packet.Length;
                    this.packetPosition = (this.packetPosition+1)%plen;
                    this.packet[this.packetPosition] = data._Bytes[rawDataIndex];                        
                    rawDataIndex = (rawDataIndex + 1) % data._Bytes.Length;

                    if ((this.packet[this.packetPosition] == 'D') &&
                         (this.packet[((this.packetPosition-1+plen) % plen)] == 'M') &&
                         (this.packet[((this.packetPosition-2+plen) % plen)] == 'C'))
                    {
                        CommandModeEnterResponse response = new CommandModeEnterResponse(this._ID);
                        Response.ResponseArgs e = new Response.ResponseArgs();
                        e._Response = response;
                        FireEvent(e);                         
                    }else if ((this.packet[this.packetPosition] == '8') &&
                      (this.packet[((this.packetPosition - 1 + plen) % plen)] == '3') )
                        {
                            BaudRateResponse response = new BaudRateResponse(this._ID);
                            response._BaudRate = "38.4";
                            Response.ResponseArgs e = new Response.ResponseArgs();
                            e._Response = response;
                            FireEvent(e);
                        }

                }
                else if (this._Mode == DecoderModes.Data)
                {
                    if ((data._Bytes[rawDataIndex] & 0x80) != 0) //grab the next 6 bytes
                    {
                        this.packetPosition = 0;
                        this.headerSeen = true;
                        int headerByte = ((byte)(((byte)data._Bytes[rawDataIndex]) << 1)) >> 6;
                        this.timestamp = data._Timestamp[rawDataIndex];
                        if (headerByte == 0)
                        {
                            bytesToRead = WocketsAccelerationData.NUM_RAW_BYTES;
                            packetType = SensorDataType.ACCEL;
                        }
                        else if (headerByte == 2)
                        {

                            int opcode = (((byte)data._Bytes[rawDataIndex]) & 0x1f);
                            switch (opcode)
                            {
                                case 0:
                                    bytesToRead = 3;
                                    packetType = SensorDataType.BATTERYLEVEL;
                                    break;
                                case 0x04:
                                    bytesToRead = 10;
                                    packetType = SensorDataType.CALIBRATION_VALUES;
                                    break;
                                case 0x01:
                                    bytesToRead = 4;
                                    packetType = SensorDataType.PACKET_COUNT;
                                    break;
                                default:
                                    break;
                            }
                          
                        }
                    }

                    if ((this.headerSeen == true) && (this.packetPosition < bytesToRead))
                        this.packet[this.packetPosition] = data._Bytes[rawDataIndex];

                    this.packetPosition++;
                    rawDataIndex = (rawDataIndex + 1) % data._Bytes.Length;


                    if ((this.packetPosition == bytesToRead)) //a full packet was received
                    {
                        if (packetType == SensorDataType.ACCEL)
                        {

                            short x = (short)((((short)(this.packet[0] & 0x03)) << 8) | (((short)(this.packet[1] & 0x7f)) << 1) | (((short)(this.packet[2] & 0x40)) >> 6));
                            short y = (short)((((short)(this.packet[2] & 0x3f)) << 4) | (((short)(this.packet[3] & 0x78)) >> 3));
                            short z = (short)((((short)(this.packet[3] & 0x07)) << 7) | ((short)(this.packet[4] & 0x7f)));
                            double ts = 0;
                            ///if (this._ExpectedPacketCount == 0)
                                ts = WocketsTimer.GetUnixTime();
                            /*else
                            {
                                if (this._ReferenceTime<1)                                
                                    this._ReferenceTime=((Receivers.RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._ConnectionTime-(25.0*2401.0);
                                ts = this._ReferenceTime + 25.0;
                            }*/
                            

                            if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)
                            {
                                int bufferHead = this.head;
                                WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[bufferHead]);
                                datum.Reset();
                                datum.UnixTimeStamp = ts;

                                //copy raw bytes
                                for (int i = 0; (i < bytesToRead); i++)
                                    datum.RawBytes[i] = this.packet[i];
                                datum.Type = SensorDataType.ACCEL;
                                //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                                datum.SensorID = (byte)sourceSensor;
                                datum.X = x;
                                datum.Y = y;
                                datum.Z = z;


                                if (bufferHead >= (BUFFER_SIZE - 1))
                                    bufferHead = 0;
                                else
                                    bufferHead++;
                                this.head = bufferHead;
                            }
#if (PocketPC)
                        else if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
                        {
                            this.sdata.Write(BitConverter.GetBytes(ts), 0, sizeof(double));
                            //this.head+=sizeof(double);
                            this.sdata.Write(BitConverter.GetBytes(x), 0, sizeof(short));
                            //this.head+=sizeof(short);
                            this.sdata.Write(BitConverter.GetBytes(y), 0, sizeof(short));
                            //this.head+=sizeof(short);
                            this.sdata.Write(BitConverter.GetBytes(z), 0, sizeof(short));
                            //this.head+=sizeof(short);


                            if (this.head >= (BUFFER_SIZE - 1))
                            {
                                //bufferHead = 0;
                                this.head = 0;
                                this.sdata.Seek(0, System.IO.SeekOrigin.Begin);
                            }
                            else
                                this.head++;

                            this.shead.Seek(0, System.IO.SeekOrigin.Begin);
                            this.shead.Write(BitConverter.GetBytes(this.head), 0, sizeof(int));
                        }
#endif

                            // this.head++;



                            numDecodedPackets++;

                            this.packetPosition = 0;
                            this.headerSeen = false;


                            lastTimestamp = ts;
                        }
                        else if (packetType == SensorDataType.BATTERYLEVEL)
                        {

                            BatteryResponse br = new BatteryResponse(this._ID);
                            for (int i = 0; (i < bytesToRead); i++)
                                br.RawBytes[i] = this.packet[i];
                            br.BatteryLevel = (((int)this.packet[1]) << 3) | ((this.packet[2] >> 4) & 0x07);
                            Logger.Warn("BT," + br.SensorID + "," + br.BatteryLevel);
                            Response.ResponseArgs e = new Response.ResponseArgs();
                            e._Response = br;
                            FireEvent(e);

                        }
                        else if (packetType == SensorDataType.CALIBRATION_VALUES)
                        {

                            int x1g = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                            int x1ng = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                            int y1g = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                            int y1ng = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                            int z1g = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                            int z1ng = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);
                        }
                        else if (packetType == SensorDataType.PACKET_COUNT)
                        {
                            //#define m_PACKET_COUNT_BYTE1(count)		(count>>9)
//#define m_PACKET_COUNT_BYTE2(count)		((count>>2) & 0x7f)
//#define m_PACKET_COUNT_BYTE3(count)		((count & 0x03)<<5)
                            this._ExpectedPacketCount= 0;
                            this._ExpectedPacketCount = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) |
                                ((this.packet[3] & 0x60) >> 5);
                        }
                    }

                }
            }
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

            if ((xNode.Name == WocketsDecoder.DECODER_ELEMENT))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if ((xAttribute.Name == WocketsDecoder.TYPE_ATTRIBUTE) && (xAttribute.Value != WocketsDecoder.WOCKETS_TYPE))
                        throw new Exception("XML Parsing error - wockets decoder parsing a decoder of a different type "+xAttribute.Value);
                    else if (xAttribute.Name == WocketsDecoder.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);  
                }
            }
        }
        #endregion Serialization Methods
    }
}
