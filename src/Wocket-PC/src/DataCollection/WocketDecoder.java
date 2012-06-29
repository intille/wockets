package DataCollection;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
//import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.TimeZone;
import bafFormat.BafEncoder;
import bafFormat.BafEncoder;

import wockets.data.SensorDataType;
import wockets.data.WocketData;
import wockets.data.WocketParam;
import wockets.data.commands.CommandTypes;
import wockets.data.commands.Commands;
import wockets.data.responses.*;
import wockets.data.types.Sensitivity;
import wockets.data.types.TransmissionMode;
import wockets.utils.CircularBuffer;
import wockets.utils.WocketsTimer;


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
	
	SensorDataType packetType;
	private ResponseTypes responseType;
	public int _ActivityCountOffset = 0;
	
    private int prevx = 0;
    private int prevy = 0;
    private int prevz = 0;
    private Date prev_time = new Date();
    private BafEncoder bafEncoder = new BafEncoder();
    
    public int _UncompressedPDUCount = 0;
    public int _CompressedPDUCount = 0;
    public int _ExpectedBatchCount = -1;
    public int _ExpectedSamplingRate = 0;
    public int _LastActivityCountIndex = -1;
    public AC_RSP[] _ActivityCounts = new AC_RSP[960];
    private double ac_unixtime = 0;
    private double acc_count = 0;
    private double ac_refseq = 0;
    private double ac_delta = 0;
    public int _ACIndex = 0;
    public int _ActivityCountIndex = 0;       
      
    private int head = 0;
    private int bytesToRead = 0;
    
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
    
	public int Decode(int sourceSensor, CircularBuffer data,int start,int end)
    {
		int temp =0;
		return temp;
	}	
    
    @Override
    public void Load(FileInputStream br) throws IOException {
    	
    }
        
    
    //******************************Decode**********************************************************************************************
    
	public void Decode(int sourceSensor, byte[] data, int end, WocketParam sr) {
		
		//SimpleDateFormat _DateFormat_log = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");			
		int rawDataIndex = head;
		int length = end;
		
		while ((rawDataIndex != length)) {
			// System.out.print("\t data["+rawDataIndex+"]:"+(data[rawDataIndex]) );
			if (data[rawDataIndex] != 0xff) {

				if (((data[rawDataIndex]) & 0x80) != 0) {// Header:First byte of a packet				
					this.packetPosition = 0;
					this.headerSeen = true;
					packetType = SensorDataType.values()[((data[rawDataIndex] << 1) & 0xff) >> 6];
					// System.out.println("packetType:"+ packetType );
					bytesToRead = DefineByteToRead(packetType,
							data[rawDataIndex]);
					// System.out.println("bytesToRead:"+ bytesToRead );
				}

				if ((this.headerSeen == true)
						&& (this.packetPosition < bytesToRead)) {
					this.packet[this.packetPosition] = data[rawDataIndex];
				}

				this.packetPosition++;

				if ((this.packetPosition == bytesToRead)) {// a full packet was received
					// System.out.println("one packet of "+ packetType
					// +" received compeletly");
					if ((packetType == SensorDataType.UNCOMPRESSED_DATA_PDU)
							|| (packetType == SensorDataType.COMPRESSED_DATA_PDU)) {
						
						// ****************calculating the Sampling rate
						Calendar logDt = Calendar.getInstance();
						Date current_time = logDt.getTime();
						long diff = current_time.getTime()
								- prev_time.getTime();
						sr.counter++;
						sr.total_time = sr.total_time + diff;
						// System.out.println("sr.total_time in decoder"+sr.total_time);
						prev_time = current_time;
						if (sr.total_time != 0) {
							long temp1 = sr.counter * 100000;
							double temp2 = temp1 / sr.total_time;
							temp1 = (long) (temp2);
							sr.samplingRate = temp1 / 100.0;
						}
						if (sr.total_time >= 60000) {
							sr.counter = 0;
							sr.total_time = 0;
							sr.minute++;
							sr.flag = 1;
						}

						// ***********************Decoding the data***********
						sr.data_flag = 1;
						bytesToRead = 0;
						short x = 0;
						short y = 0;
						short z = 0;

						if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU) {
							x = (short) ((((int) ((int) this.packet[0] & 0x03)) << 8)
									| (((int) ((int) this.packet[1] & 0x7f)) << 1) | (((int) ((int) this.packet[2] & 0x40)) >> 6));
							y = (short) ((((int) ((int) this.packet[2] & 0x3f)) << 4) | (((int) ((int) this.packet[3] & 0x78)) >> 3));
							z = (short) ((((int) ((int) this.packet[3] & 0x07)) << 7) | ((int) ((int) this.packet[4] & 0x7f)));
							_UncompressedPDUCount++;
						} else {
							x = (short) (((this.packet[0] & 0x0f) << 1) | ((this.packet[1] & 0x40) >> 6));
							x = ((((short) ((this.packet[0] >> 4) & 0x01)) == 1) ? ((short) (prevx + x))
									: ((short) (prevx - x)));
							y = (short) (this.packet[1] & 0x1f);
							y = ((((short) ((this.packet[1] >> 5) & 0x01)) == 1) ? ((short) (prevy + y))
									: ((short) (prevy - y)));
							z = (short) ((this.packet[2] >> 1) & 0x1f);
							z = ((((short) ((this.packet[2] >> 6) & 0x01)) == 1) ? ((short) (prevz + z))
									: ((short) (prevz - z)));
							_CompressedPDUCount++;
						}

						Logger.log(this._ID, x + "," + y + "," + z );
						sr.x = x;
						sr.y = y;
						sr.z = z;
						prevx = x;
						prevy = y;
						prevz = z;
						bafEncoder.encodeAndSaveData(logDt, (int) x, (int) y, (int) z, "007");

						//numDecodedPackets++;
					} else if (packetType == SensorDataType.RESPONSE_PDU) {
						DecodeResponce(responseType, bytesToRead, sr);
					}
					this.packetPosition = 0;
					this.headerSeen = false;
					bytesToRead = 0;
				}// end of processing one complete packet
			}
			rawDataIndex++;
			if (rawDataIndex == data.length) {
				rawDataIndex = 0;
			}			
		}// End while
		
		head = rawDataIndex;		
	}
    
    //**************************DefineByteToRead***********************************
    public int DefineByteToRead(SensorDataType packetType, byte pack_header){
    	int bytesToRead = 0;
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
				responseType = ResponseTypes.values()[((int)(pack_header & 0x1f))];
				//System.out.println("responseType:"+ responseType );
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
		} //End switch(packetType)
    	return bytesToRead;
    }
    
    
    //*************************DecodeResponce***************************************
    public void DecodeResponce (ResponseTypes responseType, int bytesToRead, WocketParam wp){
    	
    	switch (responseType)
        {
            case BL_RSP:
                BL_RSP br = new BL_RSP(this._ID);
                /*for (int i = 0; (i < bytesToRead); i++){
                    br._RawBytes[i] = this.packet[i];
                    System.out.println("packet"+i+": "+this.packet[i]);
                }*/
                System.out.println("received a BL packet");
                br._BatteryLevel = ((this.packet[1]&0x7f)<<3) | ((this.packet[2]&0x70)>>4);
                if (br._BatteryLevel>500){
                	wp.battery = br._BatteryLevel;
                	System.out.println("BL packet is correct");
                }
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
                break;

            case AC_RSP:
                AC_RSP ac = new AC_RSP(this._ID);
                for (int i = 0; (i < bytesToRead); i++)
                    ac._RawBytes[i] = this.packet[i];

                ac._SeqNum = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) | ((this.packet[3] >> 5) & 0x03);
                ac._Count = ((this.packet[3] & 0x1f) << 11) | ((this.packet[4] & 0x7f)<<4) | ((this.packet[5]>>2)&0x0f);


                //to recover from resets
                if ((this._LastActivityCountIndex!=-1) && (ac._SeqNum==0) && (((this._ActivityCounts[this._LastActivityCountIndex]._SeqNum)- ac._SeqNum)>20))
                    this._LastActivityCountIndex = -1;           
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
                /**************************
                byte[] seqNum = new byte[4];
				byte temp;
				temp = (byte)(lastSeqNum >> 8);
				seqNum[0] = (byte)WocketSensor.WOCKET_ACK_PACKET ;
				seqNum[1] = (byte)((byte)(temp >>> 1) & 0x7f);
				seqNum[2] = (byte)((byte)(temp << 6) & 0x40);
				temp = (byte)(lastSeqNum);
				seqNum[2] |= (byte)((byte)(temp >> 2) & 0x3f);
				seqNum[3] = (byte) ((byte)(temp << 5) & 0x60);
                //**************************/

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

}

