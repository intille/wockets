using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Receivers;
using Wockets.Data;
using Wockets.Data.Accelerometers;
using Wockets.Data.Types;
using Wockets.Data.Responses;
using Wockets.Utils;
using Wockets.Exceptions;


#if (PocketPC)
using Wockets.Kernel;
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
        public int _ExpectedBatchCount = -1;
        public AC_RSP[] _ActivityCounts = new AC_RSP[960];
        public int _ActivityCountIndex = 0;
        public int _LastActivityCountIndex = -1;
        public int _ExpectedSamplingRate = 0;
        public int _ActivityCountOffset = 0;
        public double _ReferenceTime = 0;

        private double batchCurrentTime = 0;
        private double batchDeltaTime = 0;
        private double lastDecodedSampleTime = 0;

        private int prevx = 0;
        private int prevy = 0;
        private int prevz = 0;

        public int _UncompressedPDUCount = 0;
        public int _CompressedPDUCount = 0;
        

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
           // if ((CurrentWockets._Controller._Mode == MemoryMode.BluetoothToLocal) || (CurrentWockets._Controller._Mode == MemoryMode.SharedToLocal))
           // {
                for (int i = 0; (i < this._Data.Length); i++)
                    this._Data[i] = new WocketsAccelerationData();
            //}
            return true;
        }

        private byte[] b6 = new byte[6];
        private byte[] b = new byte[1];
        private double lastUnixTime = 0;
        byte[] header = new byte[1];        
        byte[] pdu = new byte[5];

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

            
            int len = 0;
            if ((header[0] & 0x60) > 0)
                len = 3;
            else
                len = 5;
            if (!(br.ReadBytes(pdu, 1, len)))
                throw new Exception("Error: reading data in PLFormat file");


            int lastDecodedIndex = 0;
            //Successfully decoded a packet
            if (this.Decode(this._ID, pdu, len) == 1)
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

        private double ac_delta = 0;
        private int ac_index = 0;
        private double ac_unixtime = 0;
        private double acc_count = 0;

        public override int Decode(int sourceSensor, CircularBuffer data,int start,int end)
        {


            int rawDataIndex = start;
            int numDecodedPackets = 0;
            //int bufferHead = this.head;


            while (rawDataIndex != end)
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
                            case SensorDataType.COMPRESSED_DATA_PDU:
                                bytesToRead = 3;
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
                                    case ResponseTypes.HV_RSP:
                                    case ResponseTypes.FV_RSP:
                                        bytesToRead = 2;
                                        break;
                                    case ResponseTypes.BL_RSP:
                                    case ResponseTypes.BC_RSP:
                                    case ResponseTypes.ACC_RSP:
                                    case ResponseTypes.OFT_RSP:
                                        bytesToRead = 3;                 
                                        break;
                                    case ResponseTypes.TCT_RSP:
                                        bytesToRead = 5;
                                        break;
                                    case ResponseTypes.AC_RSP:
                                    case ResponseTypes.PC_RSP:
                                        bytesToRead = 6;
                                        break;
                                    case ResponseTypes.CAL_RSP:
                                    case ResponseTypes.BTCAL_RSP:
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
                        if ( (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)||(packetType == SensorDataType.COMPRESSED_DATA_PDU))
                        {

                            short x = 0;
                            short y = 0;
                            short z = 0;

                            if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
                            {
                                x = (short)((((short)(this.packet[0] & 0x03)) << 8) | (((short)(this.packet[1] & 0x7f)) << 1) | (((short)(this.packet[2] & 0x40)) >> 6));
                                y = (short)((((short)(this.packet[2] & 0x3f)) << 4) | (((short)(this.packet[3] & 0x78)) >> 3));
                                z = (short)((((short)(this.packet[3] & 0x07)) << 7) | ((short)(this.packet[4] & 0x7f)));
                                _UncompressedPDUCount++;
                            }
                            else
                            {
                                x = (short)(((this.packet[0] & 0x0f) << 1) | ((this.packet[1] & 0x40) >> 6));
                                x = ((((short)((this.packet[0] >> 4) & 0x01)) == 1) ? ((short)(prevx + x)) : ((short)(prevx - x)));
                                y = (short)(this.packet[1] & 0x1f);
                                y = ((((short)((this.packet[1] >> 5) & 0x01)) == 1) ? ((short)(prevy + y)) : ((short)(prevy - y)));
                                z = (short)((this.packet[2] >> 1) & 0x1f);
                                z = ((((short)((this.packet[2] >> 6) & 0x01)) == 1) ? ((short)(prevz + z)) : ((short)(prevz - z)));
                                _CompressedPDUCount++;
                            }

                            prevx = x;
                            prevy = y;
                            prevz = z;
                            double ts = 0;

                            //Use the high precision timer
                            if (CurrentWockets._Controller._TMode == TransmissionMode.Continuous)
                                ts = WocketsTimer.GetUnixTime();
                            else // use date time now assuming suspension is possible
                            {
                                ts = batchCurrentTime;
                                batchCurrentTime += batchDeltaTime;
                            }
                            this.TotalSamples++;                    

                            //if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)
                           // if (CurrentWockets._Controller._Mode== MemoryMode.BluetoothToLocal)
                            //{
                                int bufferHead = this.head;
                                WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[bufferHead]);
                                datum.Reset();                                
                                datum.UnixTimeStamp = ts;

                                //copy raw bytes
                                for (int i = 0; (i < bytesToRead); i++)
                                    datum.RawBytes[i] = this.packet[i];
                                if (bytesToRead == 3)
                                    datum._Type = SensorDataType.COMPRESSED_DATA_PDU;
                                else
                                    datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                                datum._Length = bytesToRead;
                                //datum.RawBytes[0] = (byte)(((datum.RawBytes[0])&0xc7)|(sourceSensor<<3));
                                datum._SensorID = (byte)sourceSensor;
                                datum._X = x;
                                datum._Y = y;
                                datum._Z = z;

#if (PocketPC)
                                if ((CurrentWockets._Controller._TMode== TransmissionMode.Continuous) && (CurrentWockets._Controller._Mode == MemoryMode.BluetoothToShared))//if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
                                {
                                    this.sdata.Write(BitConverter.GetBytes(ts), 0, sizeof(double));
                                    //this.head+=sizeof(double);
                                    this.sdata.Write(BitConverter.GetBytes(x), 0, sizeof(short));
                                    //this.head+=sizeof(short);
                                    this.sdata.Write(BitConverter.GetBytes(y), 0, sizeof(short));
                                    //this.head+=sizeof(short);
                                    this.sdata.Write(BitConverter.GetBytes(z), 0, sizeof(short));
                                }
#endif
                                if (bufferHead >= (BUFFER_SIZE - 1))
                                {
                                    bufferHead = 0;
#if (PocketPC)
                                    if (CurrentWockets._Controller._TMode == TransmissionMode.Continuous)
                                     this.sdata.Seek(0, System.IO.SeekOrigin.Begin);
#endif
                                }
                                else
                                    bufferHead++;
                                this.head = bufferHead;
#if (PocketPC)
                                if (CurrentWockets._Controller._TMode == TransmissionMode.Continuous)
                                {
                                    this.shead.Seek(0, System.IO.SeekOrigin.Begin);
                                    this.shead.Write(BitConverter.GetBytes(this.head), 0, sizeof(int));

                                }
#endif
                           /// }
#if (PocketPC)
                            /*else 
                            if (CurrentWockets._Controller._Mode == MemoryMode.BluetoothToShared)//if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
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
                        }*/
#endif


                            numDecodedPackets++;
                            
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
#if (PocketPC)
                                    Core.WRITE_BATTERY_LEVEL(br);
                                    //this.events.Add(br);
#endif
                                 //   FireEvent(br);
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
#if (PocketPC)
                                    Core.WRITE_CALIBRATION(cal);
                                    //this.events.Add(cal);
#endif
                                   // FireEvent(cal);
                                    break;
                                case ResponseTypes.BTCAL_RSP:
                                    BTCAL_RSP btcal = new BTCAL_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        btcal.RawBytes[i] = this.packet[i];
                                    btcal._CAL100 = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                                    btcal._CAL80 = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                                    btcal._CAL60 = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                                    btcal._CAL40 = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                                    btcal._CAL20 = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                                    btcal._CAL10 = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);
                                    //FireEvent(btcal);
                                    //this.events.Add(btcal);
                                    break;
                                case ResponseTypes.SR_RSP:
                                    SR_RSP sr = new SR_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        sr.RawBytes[i] = this.packet[i];
                                    sr._SamplingRate= (this.packet[1]&0x7f);                  
                                    this._ExpectedSamplingRate = sr._SamplingRate;
#if (PocketPC)
                                    Core.WRITE_SAMPLING_RATE(sr);
                                    //this.events.Add(sr);
#endif
                                    //FireEvent(sr);
                                    break;
                                case ResponseTypes.BP_RSP:
                                    BP_RSP bp = new BP_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        bp.RawBytes[i] = this.packet[i];
                                    bp._Percent= (this.packet[1] & 0x7f);
#if (PocketPC)
                                    Core.WRITE_BATTERY_PERCENT(bp);
                                    //this.events.Add(bp);
#endif
                                    //FireEvent(bp);
                                    break;
                                case ResponseTypes.TM_RSP:
                                    TM_RSP tm = new TM_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        tm.RawBytes[i] = this.packet[i];
                                    tm._TransmissionMode = (TransmissionMode)((this.packet[1]>>4) & 0x07);
#if (PocketPC)
                                    Core.WRITE_TRANSMISSION_MODE(tm);
                                    //this.events.Add(tm);
#endif
                                    //FireEvent(tm);
                                    break;

                                case ResponseTypes.SENS_RSP:
                                    SENS_RSP sen = new SENS_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        sen.RawBytes[i] = this.packet[i];
                                    sen._Sensitivity = (Sensitivity)((this.packet[1] >> 4) & 0x07);
#if (PocketPC)
                                    Core.WRITE_SENSITIVITY(sen);
                                    //this.events.Add(sen);
#endif
                                    //FireEvent(sen);
                                    break;
                                case ResponseTypes.PC_RSP:
                                    PC_RSP pc = new PC_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        pc.RawBytes[i] = this.packet[i];
                                    pc._Count = ((this.packet[1] & 0x7f) << 25) | ((this.packet[2] & 0x7f) << 18) | ((this.packet[3] & 0x7f) << 11) | ((this.packet[4] & 0x7f) << 4) | ((this.packet[5] & 0x7f) >> 3);
#if (PocketPC)
                                    Core.WRITE_PDU_COUNT(pc);
                                    //this.events.Add(pc);      
#endif                 
                                    //FireEvent(pc);
                                    break;
                                case ResponseTypes.PDT_RSP:
                                    PDT_RSP pdt = new PDT_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        pdt.RawBytes[i] = this.packet[i];
                                    pdt._Timeout = (this.packet[1] & 0x7f); 
                                   // FireEvent(pdt);
                                    break;

                                case ResponseTypes.HV_RSP:
                                    HV_RSP hv = new HV_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        hv.RawBytes[i] = this.packet[i];
                                    hv._Version = (this.packet[1] & 0x7f);
                                   // FireEvent(hv);
                                    break;
                                case ResponseTypes.FV_RSP:
                                    FV_RSP fv = new FV_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        fv.RawBytes[i] = this.packet[i];
                                    fv._Version = (this.packet[1] & 0x7f);
                                   // FireEvent(fv);
                                    break;
                                case ResponseTypes.BC_RSP:
                                    BC_RSP bc = new BC_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        bc.RawBytes[i] = this.packet[i];
                                    bc._Count = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                    this._ExpectedBatchCount = bc._Count;
                                    //Compute the start time and delta for timestamping the data
                                    double calculated_startTime=((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime;
                                    //attempt correcting using the sampling rate, check if the
                                    // first sample has a timestamp greater than the last timestamped
                                    // sample... if that is the case continue
                                    // if it is not the case then temporarily alter the delta value
                                    // to fit within the start time and end time for the samples
                                    // this is necessary to avoid overspreading the samples when disconnections
                                    // occur
                                    calculated_startTime -= ((1000.0 / this._ExpectedSamplingRate) * bc._Count);

                                    // Only use the ideal sampling rate to spread out the signal if
                                    // there is a huge gap with the previous transmission
                                    if ((calculated_startTime > lastDecodedSampleTime) && ((calculated_startTime - lastDecodedSampleTime) >60000))
                                    {
                                        batchCurrentTime = calculated_startTime;
                                        batchDeltaTime = 1000.0 / this._ExpectedSamplingRate;
                                    }
                                    else
                                    {
                                        batchDeltaTime = (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime - lastDecodedSampleTime) / bc._Count;
                                        batchCurrentTime = lastDecodedSampleTime+batchDeltaTime;
                                    }
                                    lastDecodedSampleTime = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime;
                                   // FireEvent(bc);
                                    //this.events.Add(bc);
                                    break;

                                case ResponseTypes.AC_RSP:
                                    AC_RSP ac = new AC_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        ac.RawBytes[i] = this.packet[i];

                                    ac._SeqNum = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) | ((this.packet[3] >> 5) & 0x03);
                                    ac._Count = ((this.packet[3] & 0x1f) << 11) | ((this.packet[4] & 0x7f)<<4) | ((this.packet[5]>>2)&0x0f);
                                    //First time base it on the sampling rate
                                    if (this._LastActivityCountIndex==-1)
                                    {
                                        ac_unixtime=((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0)/this._ExpectedSamplingRate) - (acc_count* 60000.0);
                                        ac_delta=60000.0;
                                    }
                                    else if (ac_delta == 0) //First sample after ACC
                                    {
                                        if (ac._SeqNum == (this._ActivityCounts[this._LastActivityCountIndex]._SeqNum + 1))// if the sequence number follows well
                                        {

                                            ac_delta = (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime - this._ActivityCounts[this._LastActivityCountIndex]._TimeStamp) / acc_count;
                                            ac_unixtime = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0) / this._ExpectedSamplingRate) - (acc_count * ac_delta);
                                        }
                                        else //seq numbers do not follow
                                        {
                                            ac_unixtime = ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[this._ID])._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0) / this._ExpectedSamplingRate) - (acc_count * 60000.0);
                                            ac_delta = 60000.0;
                                        }
                                    }

                                    //Has to stay here to protect against situations when a batch is sent
                                    //with some ACs that were received and others that were not
                                    ac._TimeStamp = ac_unixtime+ (++ac_index * ac_delta);

                                    //Only insert new sequence numbers
                                    // if this is the first AC or it is not equal to the previous sequence number
                                    if ((this._LastActivityCountIndex==-1) || (ac._SeqNum > this._ActivityCounts[this._LastActivityCountIndex]._SeqNum))
                                    {                 
                                        this._LastActivityCountIndex = this._ActivityCountIndex;
                                        this._ActivityCounts[this._ActivityCountIndex++] = ac;
                                        if (this._ActivityCountIndex == 960)
                                            this._ActivityCountIndex = 0;
                                    }

#if (PocketPC)
                                    Core.WRITE_ACTIVITY_COUNT(ac);
                                    //this.events.Add(ac);
#endif
                                    //FireEvent(ac);
                                    break;

                                case ResponseTypes.TCT_RSP:
                                    TCT_RSP tct = new TCT_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        tct.RawBytes[i] = this.packet[i];
                                    tct._TCT = (((this.packet[1] & 0x7f) << 1) | ((this.packet[2] >> 6) & 0x01));
                                    tct._REPS = (((this.packet[2] & 0x3f) << 2) | ((this.packet[3] >> 5) & 0x03));
                                    tct._LAST = (((this.packet[3] & 0x1f) << 3) | ((this.packet[4] >> 4) & 0x07));
#if (PocketPC)
                                    Core.WRITE_TCT(tct);
                                    //this.events.Add(tct);
#endif
                                    //FireEvent(tct);
                                    break;

                                case ResponseTypes.ACC_RSP:
                                    ACC_RSP acc = new ACC_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        acc.RawBytes[i] = this.packet[i];
                                    acc._Count = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                    ac_unixtime = 0;
                                    ac_delta = 0;
                                    ac_index = 0;
                                    acc_count=acc._Count;
                                    //this.events.Add(acc);
                                    //FireEvent(acc);
                                    break;
                                case ResponseTypes.OFT_RSP:
                                    OFT_RSP offset = new OFT_RSP(this._ID);
                                    for (int i = 0; (i < bytesToRead); i++)
                                        offset.RawBytes[i] = this.packet[i];
                                    offset._Offset = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                    this._ActivityCountOffset = offset._Offset;
                                    //FireEvent(offset);
                                    //this.events.Add(offset);
                                    break;
                                default:
                                    break;
                            }
                            //if (CurrentWockets._Controller._TMode== TransmissionMode.Continuous)
                              //  FireEvents();

                        }

                        this.packetPosition = 0;
                        this.headerSeen = false;
        
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


                    if ((data[rawDataIndex] & 0x80) != 0)
                    {
                        this.packetPosition = 0;
                        this.headerSeen = true;
                        packetType = (SensorDataType)((int)((byte)(((byte)data[rawDataIndex]) << 1) >> 6));                        
                        switch (packetType)
                        {
                            case SensorDataType.UNCOMPRESSED_DATA_PDU:
                                bytesToRead = 5;
                                break;
                            case SensorDataType.COMPRESSED_DATA_PDU:
                                bytesToRead = 3;
                                break;
                            case SensorDataType.RESPONSE_PDU:
                                responseType = (ResponseTypes)((int)(((byte)data[rawDataIndex]) & 0x1f));
                                switch (responseType)
                                {
                                    case ResponseTypes.BP_RSP:
                                    case ResponseTypes.SENS_RSP:
                                    case ResponseTypes.SR_RSP:
                                    case ResponseTypes.ALT_RSP:
                                    case ResponseTypes.PDT_RSP:
                                    case ResponseTypes.TM_RSP:
                                    case ResponseTypes.HV_RSP:
                                    case ResponseTypes.FV_RSP:
                                        bytesToRead = 2;
                                        break;
                                    case ResponseTypes.BL_RSP:
                                    case ResponseTypes.BC_RSP:
                                        bytesToRead = 3;
                                        break;
                                    case ResponseTypes.PC_RSP:
                                        bytesToRead = 6;
                                        break;
                                    case ResponseTypes.CAL_RSP:
                                    case ResponseTypes.BTCAL_RSP:
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
                        this.packet[this.packetPosition] = data[rawDataIndex];


                    this.packetPosition++;
                    rawDataIndex++;


                    if ((this.packetPosition == bytesToRead)) //a full packet was received
                    {
                        WocketsAccelerationData datum = ((WocketsAccelerationData)this._Data[this.head]);
                        datum.Reset();
                        //copy raw bytes
                        for (int i = 0; (i < bytesToRead); i++)
                            datum.RawBytes[i] = this.packet[i];

                        datum.UnixTimeStamp = lastUnixTime;
                        if ( (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)||(packetType == SensorDataType.COMPRESSED_DATA_PDU))
                        {

                            short x = 0;
                            short y = 0;
                            short z = 0;

                            if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
                            {
                                              
                                datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                                x = (short)((((short)(this.packet[0] & 0x03)) << 8) | (((short)(this.packet[1] & 0x7f)) << 1) | (((short)(this.packet[2] & 0x40)) >> 6));
                                y = (short)((((short)(this.packet[2] & 0x3f)) << 4) | (((short)(this.packet[3] & 0x78)) >> 3));
                                z = (short)((((short)(this.packet[3] & 0x07)) << 7) | ((short)(this.packet[4] & 0x7f)));
                                _UncompressedPDUCount++;
                            }
                            else
                            {
                                                            
                                datum._Type = SensorDataType.COMPRESSED_DATA_PDU;
                                x = (short)(((this.packet[0] & 0x0f) << 1) | ((this.packet[1] & 0x40) >> 6));
                                x = ((((short)((this.packet[0] >> 4) & 0x01)) == 1) ? ((short)(prevx + x)) : ((short)(prevx - x)));
                                y = (short)(this.packet[1] & 0x1f);
                                y = ((((short)((this.packet[1] >> 5) & 0x01)) == 1) ? ((short)(prevy + y)) : ((short)(prevy - y)));
                                z = (short)((this.packet[2] >> 1) & 0x1f);
                                z = ((((short)((this.packet[2] >> 6) & 0x01)) == 1) ? ((short)(prevz + z)) : ((short)(prevz - z)));
                                _CompressedPDUCount++;
                            }

                            prevx = x;
                            prevy = y;
                            prevz = z;
                            datum._X = (short)x;
                            datum._Y = (short)y;
                            datum._Z = (short)z;


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
