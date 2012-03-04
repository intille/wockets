package DataCollection;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Calendar;
import java.util.TimeZone;


import wockets.data.SensorDataType;
import wockets.data.WocketData;
import wockets.data.commands.CommandTypes;
import wockets.data.commands.Commands;
import wockets.data.responses.*;
import wockets.data.types.Sensitivity;
import wockets.data.types.TransmissionMode;
import wockets.utils.CircularBuffer;
import wockets.utils.WocketsTimer;

//import android.util.Log;

/**
 * @author albinali
 *
 */
public final class WocketDecoder extends Decoder 
{

	public static final String TAG = "WocketDecoder";
    public static final int BUFFER_SIZE = 3072;
    protected int packetPosition;
    private boolean headerSeen;
    public long _TotalSamples = 0;
    private long lastDecodedSampleTime = 0; 
	/**
	 * 
	 */
	public WocketDecoder(int id) 
	{
		// TODO Auto-generated constructor stub
		super(id,BUFFER_SIZE, (WocketData.NUM_RAW_BYTES > Response.MAX_RAW_BYTES) ? WocketData.NUM_RAW_BYTES : Response.MAX_RAW_BYTES);
		this.packetPosition=0;
		this.headerSeen=false;
	}

	public boolean Initialize()
	{		
		for (int i = 0; (i < this._Data.length); i++)
            this._Data[i] = new WocketData(this._ID);    
		return true;
	}
	
	public boolean Dispose(){
		return true;
	}
	
	SensorDataType packetType;
	int bytesToRead=0;
	private ResponseTypes responseType;
	public int _ActivityCountOffset = 0;
    private int prevx = 0;
    private int prevy = 0;
    private int prevz = 0;
    public int _UncompressedPDUCount = 0;
    public int _CompressedPDUCount = 0;
    public int _ExpectedBatchCount = -1;
    private long batchCurrentTime = 0;
    private long batchDeltaTime = 0;    
    public int _ExpectedSamplingRate = 0;
    public int _LastActivityCountIndex = -1;
    public AC_RSP[] _ActivityCounts = new AC_RSP[960];
    private double ac_unixtime = 0;
    private double acc_count = 0;
    private double ac_refseq = 0;
    private double ac_delta = 0;
    public int _ACIndex = 0;
    public int _ActivityCountIndex = 0;
    
    public int Decode(int sourceSensor, CircularBuffer data,int start,int end)
    {
        
    	int rawDataIndex = start;
        int numDecodedPackets = 0;
  
        while (rawDataIndex != end)
        {
        	System.out.println("data._Bytes["+rawDataIndex+"]:"+ (data._Bytes[rawDataIndex]) );
        	System.out.println(data._Bytes[rawDataIndex] & 0x80);   
        	if ((data._Bytes[rawDataIndex] & 0x80) != 0) 
                {
                    this.packetPosition = 0;
                    this.headerSeen = true;                    
                    packetType = SensorDataType.values()[(((data._Bytes[rawDataIndex]&0xff) << 1)&0xff) >> 6];                    
                    switch (packetType)
                    {
                        case UNCOMPRESSED_DATA_PDU:
                            bytesToRead = 5;
                            break;
                        case COMPRESSED_DATA_PDU:
                            bytesToRead = 3;
                            //TODO Mask the S bits
                            break;
                        case RESPONSE_PDU:
                            responseType = ResponseTypes.values()[((int)(((byte)data._Bytes[rawDataIndex]) & 0x1f))];
                            System.out.println("responseType:"+ responseType );
                            switch (responseType)
                            {
                                case BP_RSP:
                                case SENS_RSP:
                                case SR_RSP:
                                case ALT_RSP:
                                case PDT_RSP:
                                case WTM_RSP:
                                case TM_RSP:
                                case HV_RSP:
                                case FV_RSP:
                                    bytesToRead = 2;
                                    break;
                                case BL_RSP:
                                case BC_RSP:
                                case ACC_RSP:
                                case OFT_RSP:
                                    bytesToRead = 3;                 
                                    break;
                                case TCT_RSP:
                                    bytesToRead = 5;
                                    break;
                                case AC_RSP:
                                case PC_RSP:
                                    bytesToRead = 6;
                                    break;
                                case CAL_RSP:
                                case BTCAL_RSP:
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
                rawDataIndex = (rawDataIndex + 1) % data._Bytes.length;
                System.out.println("pp:"+packetPosition+"  bytes:"+bytesToRead);

                if ((this.packetPosition == bytesToRead)) //a full packet was received
                {
                    if ( (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)||(packetType == SensorDataType.COMPRESSED_DATA_PDU))
                    {
                        short x = 0;
                        short y = 0;
                        short z = 0;

                        //for each batch reinitialize the activity count sum and offset
                        if (this._ActivityCountOffset < 0)
                        {
                            acc_count = -1;
                            this._ActivityCountOffset = -1;
                        }
                      	
                        if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
                        {
                            x = (short)((((int)((int)this.packet[0] & 0x03)) << 8) | (((int)((int)this.packet[1] & 0x7f)) << 1) | (((int)((int)this.packet[2] & 0x40)) >> 6));
                            y = (short)((((int)((int)this.packet[2] & 0x3f)) << 4) | (((int)((int)this.packet[3] & 0x78)) >> 3));
                            z = (short)((((int)((int)this.packet[3] & 0x07)) << 7) | ((int)((int)this.packet[4] & 0x7f)));
                            _UncompressedPDUCount++;
                        }
                        else
                        {
                        	//TODO decode according to the S bits decoded (change masking accordingly)
                            x = (short)(((this.packet[0] & 0x0f) << 1) | ((this.packet[1] & 0x40) >> 6));
                            x = ((((short)((this.packet[0] >> 4) & 0x01)) == 1) ? ((short)(prevx + x)) : ((short)(prevx - x)));
                            y = (short)(this.packet[1] & 0x1f);
                            y = ((((short)((this.packet[1] >> 5) & 0x01)) == 1) ? ((short)(prevy + y)) : ((short)(prevy - y)));
                            z = (short)((this.packet[2] >> 1) & 0x1f);
                            z = ((((short)((this.packet[2] >> 6) & 0x01)) == 1) ? ((short)(prevz + z)) : ((short)(prevz - z)));
                            _CompressedPDUCount++;
                        }
                        System.out.println("x:"+x+"   y:"+y+ "   z:"+ z);
                        prevx = x;
                        prevy = y;
                        prevz = z;
                        long ts = 0;

                        //Use the high precision timer
//                        if (WocketsService._Controller._TransmissionMode == TransmissionMode.Continuous)
//                        {
                        	Calendar now = Calendar.getInstance();
                        	now.setTimeInMillis(System.currentTimeMillis());
                        	TimeZone tz = TimeZone.getDefault();                        	
                        	long offset = tz.getOffset(now.getTimeInMillis());
                        	ts = now.getTimeInMillis() + offset;
                        	//ts = System.currentTimeMillis();
/*                        }
                        	
                        else // use date time now assuming suspension is possible
                        {
                            ts = batchCurrentTime;
                            batchCurrentTime += batchDeltaTime;
                        }
*/                        
                        Logger.log(this._ID,x + "," + y + "," + z);
                        
                    	/*Intent myintent = new Intent(WocketsService._Context, KernelListener.class);
                		myintent.putExtra("KernelMessage",KernelMessage.Data.name());               
                		myintent.putExtra("ID",(int) this._ID);
                		myintent.putExtra("X",(int) x);
                		myintent.putExtra("Y",(int)y);
                		myintent.putExtra("Z",(int) z);
                		myintent.putExtra("TS", ts);
                		WocketsService._Context.sendBroadcast(myintent);
                        */
                        this._TotalSamples++;                    
                        
                        //TODO check for transmission mode	
                        //if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)
                       // if (CurrentWockets._Controller._Mode== MemoryMode.BluetoothToLocal)
                        //{
                            int bufferHead = this._Head;
                            WocketData datum = ((WocketData)this._Data[bufferHead]);
                            datum.Reset();                                
                            datum._UnixTimeStamp = ts;

                            //copy raw bytes
                            for (int i = 0; (i < bytesToRead); i++)
                                datum._RawBytes[i] = this.packet[i];
                            if (bytesToRead == 3)
                                datum._Type = SensorDataType.COMPRESSED_DATA_PDU;
                            else
                                datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
                            datum._Length = bytesToRead;
                            datum._SensorID = (byte)sourceSensor;
                            datum._X = x;
                            datum._Y = y;
                            datum._Z = z;

                            if (bufferHead >= (BUFFER_SIZE - 1))                            
                                bufferHead = 0;
                            else
                                bufferHead++;
                            this._Head = bufferHead;
                            numDecodedPackets++;                        
                    }
                    else if (packetType == SensorDataType.RESPONSE_PDU)
                    {

                        switch (responseType)
                        {
                            case BL_RSP:
                                BL_RSP br = new BL_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    br._RawBytes[i] = this.packet[i];
                                br._BatteryLevel = (((int)this.packet[1]) << 3) | ((this.packet[2] >> 4) & 0x07);                                
                                break;                                
                            case CAL_RSP:
                                CAL_RSP cal = new CAL_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    cal._RawBytes[i] = this.packet[i];
                                cal._X1G = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                                cal._XN1G = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                                cal._Y1G = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                                cal._YN1G = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                                cal._Z1G = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                                cal._ZN1G = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);
                                break;
                            case BTCAL_RSP:
                                BTCAL_RSP btcal = new BTCAL_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    btcal._RawBytes[i] = this.packet[i];
                                btcal._CAL100 = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                                btcal._CAL80 = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                                btcal._CAL60 = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                                btcal._CAL40 = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                                btcal._CAL20 = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                                btcal._CAL10 = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);                                
                                break;
                            case SR_RSP:
                                SR_RSP sr = new SR_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    sr._RawBytes[i] = this.packet[i];
                                sr._SamplingRate= (this.packet[1]&0x7f);                  
                                this._ExpectedSamplingRate = sr._SamplingRate;
                                break;
                            case BP_RSP:
                                BP_RSP bp = new BP_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    bp._RawBytes[i] = this.packet[i];
                                bp._Percent= (this.packet[1] & 0x7f);
                                break;
                            case WTM_RSP:
                                TM_RSP tm = new TM_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    tm._RawBytes[i] = this.packet[i];
                                tm._TransmissionMode = TransmissionMode.values()[((this.packet[1]>>4) & 0x07)];
                                break;
                            case SENS_RSP:
                                SENS_RSP sen = new SENS_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    sen._RawBytes[i] = this.packet[i];
                                sen._Sensitivity = Sensitivity.values()[((this.packet[1] >> 4) & 0x07)];
                                break;
                            case PC_RSP:
                                PC_RSP pc = new PC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    pc._RawBytes[i] = this.packet[i];
                                pc._Count = ((this.packet[1] & 0x7f) << 25) | ((this.packet[2] & 0x7f) << 18) | ((this.packet[3] & 0x7f) << 11) | ((this.packet[4] & 0x7f) << 4) | ((this.packet[5] & 0x7f) >> 3);
                                break;
                            case PDT_RSP:
                                PDT_RSP pdt = new PDT_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    pdt._RawBytes[i] = this.packet[i];
                                pdt._Timeout = (this.packet[1] & 0x7f);                                 
                                break;
                            case HV_RSP:
                                HV_RSP hv = new HV_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    hv._RawBytes[i] = this.packet[i];
                                hv._Version = (this.packet[1] & 0x7f);                                
                                break;
                            case FV_RSP:
                                FV_RSP fv = new FV_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    fv._RawBytes[i] = this.packet[i];
                                fv._Version = (this.packet[1] & 0x7f);                                                                 
                                break;
                            case BC_RSP:
                                BC_RSP bc = new BC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    bc._RawBytes[i] = this.packet[i];
                                bc._Count = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                this._ExpectedBatchCount = bc._Count;
                                //Compute the start time and delta for timestamping the data
/*                                long calculated_startTime=((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime;
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
                                    batchDeltaTime = 1000/ this._ExpectedSamplingRate;
                                }
                                else
                                {
                                    batchDeltaTime = (((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime - lastDecodedSampleTime) / bc._Count;
                                    batchCurrentTime = lastDecodedSampleTime+batchDeltaTime;
                                }
                                lastDecodedSampleTime = ((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime;
*/                                break;

                            case AC_RSP:
                                AC_RSP ac = new AC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    ac._RawBytes[i] = this.packet[i];

                                ac._SeqNum = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) | ((this.packet[3] >> 5) & 0x03);
                                ac._Count = ((this.packet[3] & 0x1f) << 11) | ((this.packet[4] & 0x7f)<<4) | ((this.packet[5]>>2)&0x0f);


                                //to recover from resets
                                if ((this._LastActivityCountIndex!=-1) && (ac._SeqNum==0) && (((this._ActivityCounts[this._LastActivityCountIndex]._SeqNum)- ac._SeqNum)>20))
                                    this._LastActivityCountIndex = -1;

                               /*if ((this._LastActivityCountIndex==-1) //First time base it on the sampling rate
                                    || (acc_count<this._ActivityCounts[this._LastActivityCountIndex]._SeqNum))  //accidental reset
                  
                                {
                                    ac_unixtime=((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0)/this._ExpectedSamplingRate) - (acc_count* 60000.0);
                                    ac_delta=60000.0;
                                    ac_refseq=0;
                                }
                                else if (ac_delta == 0) //First sample after ACC, handles overflow as well
                                { 
                                      ac_unixtime = this._ActivityCounts[this._LastActivityCountIndex]._TimeStamp;
                                      ac_refseq = this._ActivityCounts[this._LastActivityCountIndex]._SeqNum;
                                      ac_delta = (((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0) / this._ExpectedSamplingRate) - this._ActivityCounts[this._LastActivityCountIndex]._TimeStamp) / (acc_count - ac_refseq);                          
                                }*/

                                //Has to stay here to protect against situations when a batch is sent
                                //with some ACs that were received and others that were not
                                //ac._TimeStamp = ac_unixtime + (++_ACIndex * ac_delta);
                                ++_ACIndex;
                                ac._TimeStamp = ac_unixtime + (((ac._SeqNum-ac_refseq)+1) * ac_delta);
                               
                                Commands command = new Commands();
                                if (_ACIndex == 10)
                                        //((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver).Write(new ACK()._Bytes);
                                		command.call(CommandTypes.ACK);
                                
                                //Only insert new sequence numbers
                                // if this is the first AC or it is not equal to the previous sequence number
                                if ((this._ActivityCountOffset >= 0) && (acc_count >= 0))
                                {                                       
                                    if ((this._LastActivityCountIndex == -1) || (ac._SeqNum == (this._ActivityCounts[this._LastActivityCountIndex]._SeqNum + 1)) || ((ac._SeqNum - this._ActivityCounts[this._LastActivityCountIndex]._SeqNum + 1) > 960))
                                    {
                                        this._LastActivityCountIndex = this._ActivityCountIndex;
                                        this._ActivityCounts[this._ActivityCountIndex++] = ac;
                                        if (this._ActivityCountIndex == 960)
                                            this._ActivityCountIndex = 0;                                       
                                    }
                                }

                                break;
                            case TCT_RSP:
                                TCT_RSP tct = new TCT_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    tct._RawBytes[i] = this.packet[i];
                                tct._TCT = (((this.packet[1] & 0x7f) << 1) | ((this.packet[2] >> 6) & 0x01));
                                tct._REPS = (((this.packet[2] & 0x3f) << 2) | ((this.packet[3] >> 5) & 0x03));
                                tct._LAST = (((this.packet[3] & 0x1f) << 3) | ((this.packet[4] >> 4) & 0x07));
                                break;
                            case ACC_RSP:
                                ACC_RSP acc = new ACC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    acc._RawBytes[i] = this.packet[i];
                                acc._Count = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                ac_unixtime = 0;
                                ac_delta = 0;
                                _ACIndex = 0;
                                acc_count=acc._Count;                                
                                break;
                            case OFT_RSP:
                                OFT_RSP offset = new OFT_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    offset._RawBytes[i] = this.packet[i];
                                offset._Offset = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                this._ActivityCountOffset = offset._Offset;
                                break;
                            case TM_RSP:
                                /*TM_RSP tm = new TM_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    tm._RawBytes[i] = this.packet[i];
                                tm._TransmissionMode = TransmissionMode.values()[((this.packet[1]>>4) & 0x07)];*/
                                break;
                            default:
                                break;
                        }                                     
                    }

                    this.packetPosition = 0;
                    this.headerSeen = false;    
                }
        }
        return numDecodedPackets;
    }
    
    // reading data from PLFormat File
    private byte b;
    private byte[] b6 = new byte[6];
    private double lastUnixTime = 0;
    private byte[] header = new byte[1];
    private byte[] pdu = new byte[5];
    
    @Override
    public void Load(FileInputStream br) throws IOException
    {
    	// read timestamp
    	try
    	{
    		b = (byte) br.read();
    	}
		catch(IOException ex)
		{
			String strMsg = TAG + ":Load()\n";
			strMsg += "Error while reading first byte from PLFormat File\n";
			strMsg += ex.getMessage() + "\n";
			
			StringWriter errTrace = new StringWriter();
			ex.printStackTrace(new PrintWriter(errTrace));
			
			strMsg += errTrace.toString();
			
			Logger.error(strMsg);			
			throw new IOException("Error while reading first byte");
		}
							
    	    	
    	if(b == 255 || b == -1) //read complete timestamp
    	{
			if(br.read(b6) == -1)
				throw new IOException("Error reading full timestamp from PLFormat file");
			lastUnixTime = WocketsTimer.UnixTimeFromBytes(b6);		
    	}
    	else //read differential timestamp
    	{
    		lastUnixTime += (int) b;
    	}
    	
    	Calendar dt = Calendar.getInstance();
    	dt = WocketsTimer.DateTimeFromUnixTime(lastUnixTime);
    	
    	//read header as first byte of pdu
	
		if(br.read(header) == -1)
			throw new IOException("Error reading data in PLFormat File");
		pdu[0] = header[0];
    	
    	int len = 0 ;
    	
    	//read header to decode if compressed or uncompressed data
    	if((header[0] & 0x60) > 0)
    		len = 3;
    	else
    		len = 5;
    	
    	//read 3 or 5 bytes according to header
    
		if(br.read(pdu, 1, (len-1)) == -1)
			throw new IOException("Error reading data in PLFormat File");    		
	    	
    	int lastDecodedIndex = 0;
    	
		//successfully decoded a packet
    	if(this.Decode(this._ID, pdu, len) == 1)
    	{
    		if(this._Head == 0)
    			lastDecodedIndex = this._Data.length - 1;
    		else
    			lastDecodedIndex = this._Head - 1;
    		this._Data[lastDecodedIndex]._UnixTimeStamp = (long) lastUnixTime;
    		return;
    	}
    	else
    		throw new IOException("Failed to Decode data");    	    	    
    }
    
    
    public int Decode(int sourceSensor, byte[] data, int length)
    {
    	//System.out.println("decod is called");
    	int rawDataIndex = 0;
    	int numDecodedPackets = 0 ;    	
    	if(length != 0)
    	{
    		
    		while (rawDataIndex < length)
    		{
    			//short header_packet = (short)(data[rawDataIndex] & 0xff);
    			System.out.println("data["+rawDataIndex+"]:"+ (data[rawDataIndex]) );
    			System.out.println(data[rawDataIndex] & 0x80);
    			if(((data[rawDataIndex]) & 0x80) != 0)
    			//if((header_packet & 0x80) != 0)
    			{
    				//System.out.println("in the if");
    				this.packetPosition = 0;
    				this.headerSeen = true;    				
    				packetType = SensorDataType.values()[((data[rawDataIndex] << 1)&0xff) >> 6];
    				//packetType = SensorDataType.values()[((header_packet << 1)&0xff) >> 6];
    				System.out.println("packetType:"+ packetType );
    				switch(packetType)
    				{
	    				case UNCOMPRESSED_DATA_PDU:
	    				{
	    					bytesToRead = 5;
	    					break;
	    				}
	    				case COMPRESSED_DATA_PDU:
	    				{
	    					bytesToRead = 3;
	    					break;	    					
	    				}
	    				case RESPONSE_PDU :
	    				{	    					
	    					responseType = ResponseTypes.values()[((int)(((byte)data[rawDataIndex]) & 0x1f))];
	    					//responseType = ResponseTypes.values()[header_packet & 0x1f];
	    					System.out.println("responseType:"+ responseType );
	    					switch(responseType)
	    					{
		    					case BP_RSP:
		    					case SENS_RSP:
		    					case SR_RSP:
		    					case ALT_RSP:
		    					case PDT_RSP:
		    					case WTM_RSP:
		    					case TM_RSP:
		    					case HV_RSP:
		    					case FV_RSP:
		    						bytesToRead = 2;
		    						break;
		    					case BL_RSP:
		    					case BC_RSP:
		    						bytesToRead = 3;
		    						break;
		    					case TCT_RSP:
		    						bytesToRead = 5;
		    						break;
		    					case PC_RSP:
		    						bytesToRead = 6;
		    						break;
		    					case CAL_RSP:
		    					case BTCAL_RSP:
		    						bytesToRead = 10;
		    						break;
	    						default:
	    							break;
	    					}                                   
	    				}
	    				default:
	    					break;
    				}
    			}
    			
    			if ((this.headerSeen == true) && (this.packetPosition < bytesToRead))
    				this.packet[this.packetPosition] = data[rawDataIndex];
    			
    			this.packetPosition++;
                rawDataIndex++;
                System.out.println("pp:"+packetPosition+"  bytes:"+bytesToRead);
    			
                if ((this.packetPosition == bytesToRead)) //a full packet was received
    			{
                	System.out.println("in the if1");
                	/*WocketData datum = ((WocketData)this._Data[this._Head]);
    				datum.Reset();
    				//copy raw bytes;
    				for(int i = 0; i < bytesToRead ; i ++)    				
    					datum._RawBytes[i] = this.packet[i];    				
    				
    				datum._UnixTimeStamp = (long)lastUnixTime;*/
    				
    				if((packetType == SensorDataType.UNCOMPRESSED_DATA_PDU) || (packetType == SensorDataType.COMPRESSED_DATA_PDU))
    				{
    					System.out.println("in the if2");
    					short x  = 0;
    					short y = 0; 
    					short z = 0;
    					
    					if(packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
    					{
    						//datum._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
    						x = (short)((((int)((int)this.packet[0] & 0x03)) << 8) | (((int)((int)this.packet[1] & 0x7f)) << 1) | (((int)((int)this.packet[2] & 0x40)) >> 6));
                            y = (short)((((int)((int)this.packet[2] & 0x3f)) << 4) | (((int)((int)this.packet[3] & 0x78)) >> 3));
                            z = (short)((((int)((int)this.packet[3] & 0x07)) << 7) | ((int)((int)this.packet[4] & 0x7f)));
                            _UncompressedPDUCount++;
    					}
    					else
    					{
    						//datum._Type = SensorDataType.COMPRESSED_DATA_PDU;
    						x = (short)(((this.packet[0] & 0x0f) << 1) | ((this.packet[1] & 0x40) >> 6));
                            x = ((((short)((this.packet[0] >> 4) & 0x01)) == 1) ? ((short)(prevx + x)) : ((short)(prevx - x)));
                            y = (short)(this.packet[1] & 0x1f);
                            y = ((((short)((this.packet[1] >> 5) & 0x01)) == 1) ? ((short)(prevy + y)) : ((short)(prevy - y)));
                            z = (short)((this.packet[2] >> 1) & 0x1f);
                            z = ((((short)((this.packet[2] >> 6) & 0x01)) == 1) ? ((short)(prevz + z)) : ((short)(prevz - z)));
                            _CompressedPDUCount++;
    					}
    					
    					System.out.println("x:"+x+"   y:"+y+ "   z:"+ z);
    					Logger.log(this._ID,x + "," + y + "," + z);
                    	//System.out.println();
    					
    					prevx = x;
    					prevy = y;
    					prevz = z;
    					
    					/*datum._X = (short)x;
    					datum._Y = (short)y;
    					datum._Z = (short)z;*/
    					
    					if(this._Head >= (BUFFER_SIZE -1))
    						this._Head = 0;
    					else this._Head ++;
    					numDecodedPackets++;
    					
    					this.packetPosition = 0;
    					this.headerSeen = false;
    				}
    				else if (packetType == SensorDataType.RESPONSE_PDU)
                    {
                        switch (responseType)
                        {
                            case BL_RSP:
                                BL_RSP br = new BL_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    br._RawBytes[i] = this.packet[i];
                                br._BatteryLevel = (((int)this.packet[1]) << 3) | ((this.packet[2] >> 4) & 0x07);                                
                                break;                                
                            case CAL_RSP:
                                CAL_RSP cal = new CAL_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    cal._RawBytes[i] = this.packet[i];
                                cal._X1G = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                                cal._XN1G = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                                cal._Y1G = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                                cal._YN1G = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                                cal._Z1G = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                                cal._ZN1G = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);
                                break;
                            case BTCAL_RSP:
                                BTCAL_RSP btcal = new BTCAL_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    btcal._RawBytes[i] = this.packet[i];
                                btcal._CAL100 = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                                btcal._CAL80 = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                                btcal._CAL60 = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                                btcal._CAL40 = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                                btcal._CAL20 = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                                btcal._CAL10 = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);                                
                                break;
                            case SR_RSP:
                                SR_RSP sr = new SR_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    sr._RawBytes[i] = this.packet[i];
                                sr._SamplingRate= (this.packet[1]&0x7f);                  
                                this._ExpectedSamplingRate = sr._SamplingRate;
                                break;
                            case BP_RSP:
                                BP_RSP bp = new BP_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    bp._RawBytes[i] = this.packet[i];
                                bp._Percent= (this.packet[1] & 0x7f);
                                break;
                            case WTM_RSP:
                                TM_RSP tm = new TM_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    tm._RawBytes[i] = this.packet[i];
                                tm._TransmissionMode = TransmissionMode.values()[((this.packet[1]>>4) & 0x07)];
                                break;
                            case SENS_RSP:
                                SENS_RSP sen = new SENS_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    sen._RawBytes[i] = this.packet[i];
                                sen._Sensitivity = Sensitivity.values()[((this.packet[1] >> 4) & 0x07)];
                                break;
                            case PC_RSP:
                                PC_RSP pc = new PC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    pc._RawBytes[i] = this.packet[i];
                                pc._Count = ((this.packet[1] & 0x7f) << 25) | ((this.packet[2] & 0x7f) << 18) | ((this.packet[3] & 0x7f) << 11) | ((this.packet[4] & 0x7f) << 4) | ((this.packet[5] & 0x7f) >> 3);
                                break;
                            case PDT_RSP:
                                PDT_RSP pdt = new PDT_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    pdt._RawBytes[i] = this.packet[i];
                                pdt._Timeout = (this.packet[1] & 0x7f);                                 
                                break;
                            case HV_RSP:
                                HV_RSP hv = new HV_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    hv._RawBytes[i] = this.packet[i];
                                hv._Version = (this.packet[1] & 0x7f);                                
                                break;
                            case FV_RSP:
                                FV_RSP fv = new FV_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    fv._RawBytes[i] = this.packet[i];
                                fv._Version = (this.packet[1] & 0x7f);                                                                 
                                break;
                            case BC_RSP:
                                BC_RSP bc = new BC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    bc._RawBytes[i] = this.packet[i];
                                bc._Count = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                this._ExpectedBatchCount = bc._Count;
                                //Compute the start time and delta for timestamping the data
/*                                long calculated_startTime=((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime;
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
                                    batchDeltaTime = 1000/ this._ExpectedSamplingRate;
                                }
                                else
                                {
                                    batchDeltaTime = (((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime - lastDecodedSampleTime) / bc._Count;
                                    batchCurrentTime = lastDecodedSampleTime+batchDeltaTime;
                                }
                                lastDecodedSampleTime = ((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime;
*/                                break;

                            case AC_RSP:
                                AC_RSP ac = new AC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    ac._RawBytes[i] = this.packet[i];

                                ac._SeqNum = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) | ((this.packet[3] >> 5) & 0x03);
                                ac._Count = ((this.packet[3] & 0x1f) << 11) | ((this.packet[4] & 0x7f)<<4) | ((this.packet[5]>>2)&0x0f);


                                //to recover from resets
                                if ((this._LastActivityCountIndex!=-1) && (ac._SeqNum==0) && (((this._ActivityCounts[this._LastActivityCountIndex]._SeqNum)- ac._SeqNum)>20))
                                    this._LastActivityCountIndex = -1;

                               /*if ((this._LastActivityCountIndex==-1) //First time base it on the sampling rate
                                    || (acc_count<this._ActivityCounts[this._LastActivityCountIndex]._SeqNum))  //accidental reset
                  
                                {
                                    ac_unixtime=((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0)/this._ExpectedSamplingRate) - (acc_count* 60000.0);
                                    ac_delta=60000.0;
                                    ac_refseq=0;
                                }
                                else if (ac_delta == 0) //First sample after ACC, handles overflow as well
                                { 
                                      ac_unixtime = this._ActivityCounts[this._LastActivityCountIndex]._TimeStamp;
                                      ac_refseq = this._ActivityCounts[this._LastActivityCountIndex]._SeqNum;
                                      ac_delta = (((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver)._CurrentConnectionUnixTime - ((this._ActivityCountOffset * 1000.0) / this._ExpectedSamplingRate) - this._ActivityCounts[this._LastActivityCountIndex]._TimeStamp) / (acc_count - ac_refseq);                          
                                }*/

                                //Has to stay here to protect against situations when a batch is sent
                                //with some ACs that were received and others that were not
                                //ac._TimeStamp = ac_unixtime + (++_ACIndex * ac_delta);
                                ++_ACIndex;
                                ac._TimeStamp = ac_unixtime + (((ac._SeqNum-ac_refseq)+1) * ac_delta);
                               
                                Commands command = new Commands();
                                if (_ACIndex == 10)
                                        //((RFCOMMReceiver)WocketsService._Controller._Sensors.get(this._ID)._Receiver).Write(new ACK()._Bytes);
                                		command.call(CommandTypes.ACK);
                                
                                //Only insert new sequence numbers
                                // if this is the first AC or it is not equal to the previous sequence number
                                if ((this._ActivityCountOffset >= 0) && (acc_count >= 0))
                                {                                       
                                    if ((this._LastActivityCountIndex == -1) || (ac._SeqNum == (this._ActivityCounts[this._LastActivityCountIndex]._SeqNum + 1)) || ((ac._SeqNum - this._ActivityCounts[this._LastActivityCountIndex]._SeqNum + 1) > 960))
                                    {
                                        this._LastActivityCountIndex = this._ActivityCountIndex;
                                        this._ActivityCounts[this._ActivityCountIndex++] = ac;
                                        if (this._ActivityCountIndex == 960)
                                            this._ActivityCountIndex = 0;                                       
                                    }
                                }

                                break;
                            case TCT_RSP:
                                TCT_RSP tct = new TCT_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    tct._RawBytes[i] = this.packet[i];
                                tct._TCT = (((this.packet[1] & 0x7f) << 1) | ((this.packet[2] >> 6) & 0x01));
                                tct._REPS = (((this.packet[2] & 0x3f) << 2) | ((this.packet[3] >> 5) & 0x03));
                                tct._LAST = (((this.packet[3] & 0x1f) << 3) | ((this.packet[4] >> 4) & 0x07));
                                break;
                            case ACC_RSP:
                                ACC_RSP acc = new ACC_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    acc._RawBytes[i] = this.packet[i];
                                acc._Count = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                ac_unixtime = 0;
                                ac_delta = 0;
                                _ACIndex = 0;
                                acc_count=acc._Count;                                
                                break;
                            case OFT_RSP:
                                OFT_RSP offset = new OFT_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    offset._RawBytes[i] = this.packet[i];
                                offset._Offset = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                                this._ActivityCountOffset = offset._Offset;
                                break;
                            case TM_RSP:
                                /*TM_RSP tm = new TM_RSP(this._ID);
                                for (int i = 0; (i < bytesToRead); i++)
                                    tm._RawBytes[i] = this.packet[i];
                                tm._TransmissionMode = TransmissionMode.values()[((this.packet[1]>>4) & 0x07)];*/
                                break;
                            default:
                                break;
                        }                           
                    }
    				this.packetPosition = 0;
					this.headerSeen = false;
    			}
    		}
    	}
    	return numDecodedPackets;
    }
}
