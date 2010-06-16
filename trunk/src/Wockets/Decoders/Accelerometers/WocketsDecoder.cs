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

        public const int BUFFER_SIZE = 3072; //4096; 
        private bool headerSeen;
        private double timestamp = 0;
        private int bytesToRead = 0;
        private SensorDataType packetType;
        private ResponseTypes responseType;
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
               /* if (this._Mode == DecoderModes.Command)
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
                else */if (this._Mode == DecoderModes.Data)
                {
                           //If a PDU first byte
                    if ((data._Bytes[rawDataIndex] & 0x80) != 0) 
                    {
                        this.packetPosition = 0;
                        this.headerSeen = true;
                        packetType = (SensorDataType) ((int)( (byte)(((byte)data._Bytes[rawDataIndex]) << 1) >> 6));
                        this.timestamp = data._Timestamp[rawDataIndex];
                        switch (packetType)
                        {
                            case SensorDataType.UNCOMPRESSED_DATA_PDU:
                                bytesToRead = 5;
                                break;
                            case SensorDataType.RESPONSE_PDU:
                                responseType = (ResponseTypes)((int)(((byte)data._Bytes[rawDataIndex]) & 0x1f));
                                switch (responseType)
                                {
                                    case ResponseTypes.BP_RSP:
                                    case ResponseTypes.SENS_RSP:
                                    case ResponseTypes.SR_RSP:
                                    case ResponseTypes.ALT_RSP:
                                    case ResponseTypes.PDT_RSP:
                                    case ResponseTypes.TM_RSP:
                                        bytesToRead = 2;
                                        break;
                                    case ResponseTypes.BL_RSP:
                                        bytesToRead = 3;                 
                                        break;
                                    case ResponseTypes.PC_RSP:
                                        bytesToRead = 6;
                                        break;
                                    case ResponseTypes.CAL_RSP:
                                        bytesToRead = 10;                 
                                        break;                  
                                    default:
                                        break;
                                }
                                break;
                            default:
                                break;
                        }                       
                    }

                    if ((this.headerSeen == true) && (this.packetPosition < bytesToRead))
                        this.packet[this.packetPosition] = data._Bytes[rawDataIndex];

                    this.packetPosition++;
                    rawDataIndex = (rawDataIndex + 1) % data._Bytes.Length;


                    if ((this.packetPosition == bytesToRead)) //a full packet was received
                    {
                        if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
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
                                datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                                //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                                datum._SensorID = (byte)sourceSensor;
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
                        else if (packetType == SensorDataType.RESPONSE_PDU)
                        {

                            switch (responseType)
                            {

                                case ResponseTypes.BL_RSP:
                                    BL_RSP br = new BL_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        br.RawBytes[i] = this.packet[i];
                                    br._BatteryLevel = (((int)this.packet[1]) << 3) | ((this.packet[2] >> 4) & 0x07);                                    
                                    FireEvent(br);
                                    break;
                                case ResponseTypes.PC_RSP:
                                    this._ExpectedPacketCount = 0;
                                    this._ExpectedPacketCount = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) |
                                        ((this.packet[3] & 0x60) >> 5);
                                    break;
                                case ResponseTypes.CAL_RSP:
                                    CAL_RSP cal = new CAL_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        cal.RawBytes[i] = this.packet[i];
                                    cal._X1G = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                                    cal._XN1G = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                                    cal._Y1G = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                                    cal._YN1G = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                                    cal._Z1G = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                                    cal._ZN1G = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);                                                                        
                                    FireEvent(cal);
                                    break;
                                case ResponseTypes.SR_RSP:
                                    SR_RSP sr = new SR_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        sr.RawBytes[i] = this.packet[i];
                                    sr._SamplingRate= (this.packet[1]&0x7f);
                                    FireEvent(sr);
                                    break;
                                case ResponseTypes.TM_RSP:
                                    TM_RSP tm = new TM_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        tm.RawBytes[i] = this.packet[i];
                                    tm._TransmissionMode = (TransmissionModes)((this.packet[1]>>4) & 0x07);
                                    FireEvent(tm);
                                    break;
                                default:
                                    break;
                            }
                           
                     

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
                            packetType=SensorDataType.UNCOMPRESSED_DATA_PDU;
                        }
                        else if (headerByte==2){                         
                            bytesToRead=3;  
                            packetType=SensorDataType.COMMAND_PDU;
                        }
                    }
                    
                     if ((this.headerSeen == true) && (this.packetPosition < bytesToRead))
                         this.packet[this.packetPosition] = data[rawDataIndex];

                    this.packetPosition++;
                    rawDataIndex++;


                    if ((this.packetPosition == bytesToRead)) //a full packet was received
                    {
                        if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
                        {

                            WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[this.head]);
                            datum.Reset();
                            //copy raw bytes
                            for (int i = 0; (i < bytesToRead); i++)
                                datum.RawBytes[i] = this.packet[i];
                            datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                            //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                            datum._SensorID = (byte)sourceSensor;
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
