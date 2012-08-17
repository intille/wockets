package decoder;

import java.io.File;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.TimeZone;
import java.io.OutputStream;

import javax.swing.JTextArea;

import jsonModel.ActivityCountData;
import jsonModel.WocketInfo;
import com.google.gson.Gson;

import bafFormat.BafEncoder;
import bluetooth.PcClient;

import wockets.data.SensorDataType;
import wockets.data.WocketParam;
import wockets.data.types.ResponseTypes;
import wockets.data.types.Sensitivity;
import wockets.data.types.TransmissionMode;


public final class WocketDecoder //extends Decoder 
{
    public static final int BUFFER_SIZE = 3072;
    protected byte[] packet;
    protected int packetPosition = 0;
    private boolean headerSeen = false;
    public long _TotalSamples = 0;
	
	SensorDataType packetType;
	private ResponseTypes responseType;
	public int activityCountOffset = 0;
	public int batchCount = -1;
    public int samplingRate = 0;   
	int acc_count = 0;
	
    private int prevx = 0;
    private int prevy = 0;
    private int prevz = 0;
    private BafEncoder bafEncoder = new BafEncoder();    
              
    private int head = 0;
    private int bytesToRead = 0;
    private int lastSN = -1;  
    int prevHour = -1;
    
    //*************************************************Decode***************************************************************************    
	public void Decode(byte[] data, int end, WocketParam sr, String ID, int lastSeqNum, JTextArea textArea) {		
		Calendar logDt = Calendar.getInstance();
		//logDt.setTimeZone(TimeZone.getTimeZone("GMT-4"));
		SimpleDateFormat dateFormat = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");
		textArea.append(dateFormat.format(logDt.getTime()) + "\n");
        textArea.update(textArea.getGraphics());
		int uncompressedPDUCount = 0;
	    int compressedPDUCount = 0;
		int rawDataIndex = head;
		int length = end;
		int sec = -1;
		int sumx=0, sumy=0, sumz=0, counter = 0;
		while ((rawDataIndex != length)) {
			
			if (((data[rawDataIndex]) & 0x80) != 0) {// Header:First byte of a packet				
				packetPosition = 0;
				headerSeen = true;
				packetType = SensorDataType.values()[((data[rawDataIndex] << 1) & 0xff) >> 6];
				bytesToRead = DefineByteToRead(packetType,data[rawDataIndex]);
				packet = new byte[bytesToRead];
			}

			if ((headerSeen == true) && (packetPosition < bytesToRead)) {
				packet[packetPosition] = data[rawDataIndex];
			}

			packetPosition++;

			if ((packetPosition == bytesToRead)) {// a full packet is received
				// -----------------------Decoding raw data packets-------------------------------------
				if ((packetType == SensorDataType.UNCOMPRESSED_DATA_PDU) || (packetType == SensorDataType.COMPRESSED_DATA_PDU)) {
					bytesToRead = 0;
					short x = 0;
					short y = 0;
					short z = 0;
															    	
					if (packetType == SensorDataType.UNCOMPRESSED_DATA_PDU) {
						x = (short) ((((int) ((int) this.packet[0] & 0x03)) << 8) | (((int) ((int) this.packet[1] & 0x7f)) << 1) | (((int) ((int) this.packet[2] & 0x40)) >> 6));
						y = (short) ((((int) ((int) this.packet[2] & 0x3f)) << 4) | (((int) ((int) this.packet[3] & 0x78)) >> 3));
						z = (short) ((((int) ((int) this.packet[3] & 0x07)) << 7) | ((int) ((int) this.packet[4] & 0x7f)));
						uncompressedPDUCount++;
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
						compressedPDUCount++;
					}
					// -----------------------saving raw data----------------------
					long timeStamp = (long)logDt.getTimeInMillis() - (long)(batchCount * 25);
			    	batchCount --;
			    	//GregorianCalendar temp = new GregorianCalendar();
			    	Calendar temp = Calendar.getInstance();
			    	temp.setTimeZone(TimeZone.getTimeZone("GMT"));
			    	temp.setTimeInMillis(timeStamp);	
			    	//saveRawData(temp, ID, x + "," + y + "," + z );	
					bafEncoder.encodeAndSaveData(temp, (int) x, (int) y, (int) z, ID);
					
					prevx = x;
					prevy = y;
					prevz = z;
					
					// -------------------saving 1-sec mean of raw data--------------
					if (sec == -1)
						sec = temp.getTime().getSeconds();
					else if (sec != temp.getTime().getSeconds()){
						//saveMean(temp, ID, sumx/counter + "," + sumy/counter + "," + sumz/counter );
						sumx = sumy = sumz = counter = 0;
						sec = temp.getTime().getSeconds();
					}
					sumx += x;
					sumy += y;
					sumz += z;
					counter ++;

				// -----------------------Decoding other packets-------------------------------------
				} else if (packetType == SensorDataType.RESPONSE_PDU) {
					DecodeResponce(responseType, bytesToRead, sr, ID, lastSeqNum, logDt, textArea);
				}
				this.packetPosition = 0;
				this.headerSeen = false;
				bytesToRead = 0;
			}// end of processing one complete packet
			
			rawDataIndex++;
			if (rawDataIndex == data.length) {
				rawDataIndex = 0;
			}			
		}// End while
		
		head = rawDataIndex;		
		sr.uncompressedCount = uncompressedPDUCount;
		sr.compressedCount = compressedPDUCount;
		textArea.append("received " + (lastSN - lastSeqNum) + " summary data\n");
        textArea.update(textArea.getGraphics());
		sr.last_seqNumber = lastSN; 		
	}
    
    //**************************Define Byte To Read***********************************
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
					case ACC_RSP:
					case OFT_RSP:
						bytesToRead = 3;
						break;
					case BC_RSP:
						bytesToRead = 4;
						break;
					case TCT_RSP:
						bytesToRead = 5;
						break;
					case PC_RSP:
					case AC_RSP:
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
    
    
    //*************************Decode Responce***************************************
    public void DecodeResponce (ResponseTypes responseType, int bytesToRead, WocketParam wp, String id, int lastSeqNum, Calendar logDt, JTextArea textArea ){
    	
    	switch (responseType){
            case BL_RSP:
                int batteryLevel = ((packet[1] & 0x7f) << 3) | ((packet[2] & 0x70) >> 4);
                if (batteryLevel > 500){
                	//wp.battery = br._BatteryLevel;
                	System.out.println("Battery Level: "+ batteryLevel);
                	textArea.append("Battery Level: "+ batteryLevel +"\n");
                    textArea.update(textArea.getGraphics());
                	if (batteryLevel < 600){
	                	textArea.append("Wocket's Battery is low. Swap the Wocket.\n");
	                    textArea.update(textArea.getGraphics());
	                    PcClient.beepRunnable.run();
	                }
                }
                break;  
                
            case CAL_RSP:
                int x1G  = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                int xN1G = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                int yY1G = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                int yN1G = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                int z1G  = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                int zN1G = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3);
                System.out.println("Accelerometer Calibration values:\n x1G:"+  x1G + "\nxN1G: "+ xN1G + "\nyY1G: "+ yY1G + "\n:yN1G " + yN1G + "\nz1G:" + z1G + "\nzN1G: "+ zN1G);
                break;
                
            case BTCAL_RSP:
                int cAL100 = ((this.packet[1] & 0x7f) << 3) | ((this.packet[2] & 0x70) >> 4);
                int cAL80 = ((this.packet[2] & 0x0f) << 6) | ((this.packet[3] & 0x7e) >> 1);
                int cAL60 = ((this.packet[3] & 0x01) << 9) | ((this.packet[4] & 0x7f) << 2) | ((this.packet[5] & 0x60) >> 5);
                int cAL40 = ((this.packet[5] & 0x1f) << 5) | ((this.packet[6] & 0x7c) >> 2);
                int cAL20 = ((this.packet[6] & 0x03) << 8) | ((this.packet[7] & 0x7f) << 1) | ((this.packet[8] & 0x40) >> 6);
                int cAL10 = ((this.packet[8] & 0x3f) << 4) | ((this.packet[9] & 0x78) >> 3); 
                System.out.println("Battery Calibration values:\n cAL100:"+  cAL100 + "\ncAL80: "+ cAL80 + "\ncAL60: "+ cAL60 + "\n:cAL40 " + cAL40 + "\ncAL20:" + cAL20 + "\ncAL10: "+ cAL10);
                break;
                
            case SR_RSP:
                int samplingRate= (this.packet[1]&0x7f);                  
                this.samplingRate = samplingRate;
                break;
                
            case BP_RSP:
                int percent= (this.packet[1] & 0x7f);
                System.out.println("battery percent: "+ percent);
                break;
                
            case WTM_RSP:
                TransmissionMode transmissionMode = TransmissionMode.values()[((this.packet[1] >> 4) & 0x07)];
                break;
                
            case SENS_RSP:
            	Sensitivity sensitivity = Sensitivity.values()[((this.packet[1] >> 4) & 0x07)];
                break;
                
            case PC_RSP:
                int count = ((this.packet[1] & 0x7f) << 25) | ((this.packet[2] & 0x7f) << 18) | ((this.packet[3] & 0x7f) << 11) | ((this.packet[4] & 0x7f) << 4) | ((this.packet[5] & 0x7f) >> 3);
                System.out.println("Packet count: "+ count);
                break;
                
            case PDT_RSP:
                int timeout = (this.packet[1] & 0x7f);  
                System.out.println("timeout: "+ timeout);
                break;
                
            case HV_RSP:
                int hVersion = (this.packet[1] & 0x7f);
                System.out.println("hVersion: "+ hVersion);
                break;
                
            case FV_RSP:
                int fVersion = (this.packet[1] & 0x7f); 
                System.out.println("fVersion: "+ fVersion);
                break;
                
            case BC_RSP:
                int bCount = ((((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f)) << 2) | ((this.packet[3] & 0x60) >> 5);
                this.batchCount = bCount;
                System.out.println("BatchCount: "+ batchCount);
                break;

            case AC_RSP:
                int acSeqNum = ((this.packet[1] & 0x7f) << 9) | ((this.packet[2] & 0x7f) << 2) | ((this.packet[3] >> 5) & 0x03);
                int acCount = ((this.packet[3] & 0x1f) << 11) | ((this.packet[4] & 0x7f) << 4) | ((this.packet[5] >> 2) & 0x0f);                  
                if ( ((acSeqNum - lastSeqNum) >= 1) || (acc_count < lastSeqNum) || (lastSeqNum == -1) ) {                	
                	saveACData(acSeqNum, acCount, id, logDt);
                	lastSN = acSeqNum; 
                } 
                break;
                
            case TCT_RSP:
                int TCT = (((this.packet[1] & 0x7f) << 1) | ((this.packet[2] >> 6) & 0x01));
                int REPS = (((this.packet[2] & 0x3f) << 2) | ((this.packet[3] >> 5) & 0x03));
                int LAST = (((this.packet[3] & 0x1f) << 3) | ((this.packet[4] >> 4) & 0x07));
                System.out.println("TCT:" + TCT+ "REPS: " + REPS + "LAST: " + LAST);
                break;
                
            case ACC_RSP:
                int Wocket_last_seq = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                acc_count = Wocket_last_seq;                
                System.out.println("The last seqNumber in this package:"+ (acc_count - 1));
                break;
                
            case OFT_RSP:
                int offset = ((this.packet[1] & 0x7f) << 7) | (this.packet[2] & 0x7f);
                this.activityCountOffset = offset;
                System.out.println("Offset: "+ offset);
                break;
                
            case TM_RSP:
                int radioTransmissionMode = (this.packet[1]>>4) & 0x07;
                System.out.println("Radio Transmission Mode: "+ radioTransmissionMode);
                break;
                
            default:
                break;
        }         
    }    
  
    //********************************save AC Data***********************************     
    Gson gson = new Gson();
    WocketInfo wi = new WocketInfo();    
    
    public void saveACData(int seqNum, int summaryData, String id, Calendar logDt)
	{		
    	SimpleDateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd");
    	long diff = (long)logDt.getTimeInMillis() - (long)((acc_count - 1 - seqNum) * 60000) - (long)(activityCountOffset * 25);
    	Calendar temp = Calendar.getInstance();
    	temp.setTimeInMillis(diff);
    	Date date = temp.getTime();
    	
    	String outputFilePath = "c:/test/" + dateFormat.format(date) +"/"+date.getHours()+"/";
		File outputDir = new File(outputFilePath);
		if(!outputDir.isDirectory()){
			outputDir.mkdirs();
		}
		
	        
      //----------- json format -------------------   
      /* if (wi.someActivityCountData == null)
    	   wi.someActivityCountData = new ArrayList<ActivityCountData>();      
        ActivityCountData acData = new ActivityCountData();
        acData.activityCount = summaryData;
        //acData.macID = ID;
        acData.createTime = logDt.getTime();  
        acData.originalTime = date;			  
        wi.someActivityCountData.add(acData);
        String json = gson.toJson(wi);    
        
		String jsonFilename = outputFilePath + "Wocket."+ id + dateFormat.format(date)+ ".json";
        File jsonf = new File(jsonFilename);
        PrintWriter jsonPrintWriter = null;
        try {
            if (!(jsonf.exists())) {
            	jsonf.createNewFile();
                jsonPrintWriter = new PrintWriter(new FileWriter(jsonFilename));
            } else
            	jsonPrintWriter = new PrintWriter(new FileWriter(jsonFilename,true));
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        
        try {
        	jsonPrintWriter.append(json);
        } catch (NumberFormatException e) {
                System.out.println("Error while writing AC data in json file");
        }

        if (jsonPrintWriter != null) {
        	jsonPrintWriter.close();
        } */
      //-------------------CSV format------------------------
        String filename = getFileNameForCurrentHour(outputFilePath, logDt, id);
        File f = new File(filename);
        PrintWriter printWriter = null;
        try {
        	if (!(f.exists())) {
                f.createNewFile();
                printWriter = new PrintWriter(new FileWriter(filename));
            } else
            	printWriter = new PrintWriter(new FileWriter(filename,true));
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        SimpleDateFormat dateFormat_ac = new SimpleDateFormat("yyyy.MM.dd HH:mm:ss");
        String s = dateFormat_ac.format(date) + "," + seqNum+ "," + summaryData + "\n";
        try {
            printWriter.append(s);
        } catch (NumberFormatException e) {
                System.out.println("Error while writing AC data in csv file");
        }

        if (printWriter != null) {
        	printWriter.close();
        }        
	}
  //**********************getFileName ************************************
    private String getFileNameForCurrentHour(String path, Calendar time, final String ID){
		File dir = new File(path);
		String[] files = dir.list(new FilenameFilter() {
			
			@Override
			public boolean accept(File dir, String filename) {
				// TODO Auto-generated method stub
				return filename.contains("Wocket."+ID);
			}
		});
		if(files == null || files.length == 0) {
			SimpleDateFormat fileNameFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss");
	        String filename = path + "Wocket."+ ID + "." + fileNameFormat.format(time.getTime())+ ".csv";
			return filename;
		}
		else
			return path + files[0];
	}
    
    //*****************************save Mean raw data************************************
    public static void saveMean(Calendar gc, String id,String msg)
	{		
    	SimpleDateFormat dateFormat_raw = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");
    	dateFormat_raw.setTimeZone(TimeZone.getTimeZone("GMT")); 
    	
    	SimpleDateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd");
    	Calendar temp = Calendar.getInstance();
    	Date date = temp.getTime();
    	String outputFilePath = "c:/test/" + dateFormat.format(date) +"/";
    	
        String filename = outputFilePath+"Wocket_"+id+"_1s-RawMean.csv";
        File f = new File(filename);
        PrintWriter out = null;
        try {
                if (!(f.exists())) {
                        f.createNewFile();                    
                        out = new PrintWriter(new FileWriter(filename));
                } else
                        out = new PrintWriter(new FileWriter(filename,true));
        } catch (IOException e1) {
                e1.printStackTrace();
        }
        String s = gc.getTimeInMillis() + "," + dateFormat_raw.format(gc.getTime()) + "," + msg + "\n";
        try {
                out.append(s);
        } catch (NumberFormatException e) {
                System.out.println("Error while writing mean raw data in csv file");
        }

        if (out != null) {
                out.close();
        }		
	}
    
  //*****************************save Raw Data************************************
    public static void saveRawData(Calendar gc, String id,String msg)
	{	
    	SimpleDateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd");
    	Calendar temp = Calendar.getInstance();
    	Date date = temp.getTime();
    	String outputFilePath = "c:/test/" + dateFormat.format(date) +"/";
    	
    	String filename = outputFilePath+"Wocket_"+id+"_RawData.csv";
        File f = new File(filename);
        PrintWriter out = null;
        try {
                if (!(f.exists())) {
                        f.createNewFile();                    
                        out = new PrintWriter(new FileWriter(filename));
                } else
                        out = new PrintWriter(new FileWriter(filename,true));
        } catch (IOException e1) {
                e1.printStackTrace();
        }
        
    	String s = gc.getTimeInMillis() + "," + msg + "\n";
        try {
                //out.println(s);
                out.append(s);
        } catch (NumberFormatException e) {
                System.out.println("Error while writing raw data in csv file");
        }

        if (out != null) {
                out.close();
        }		
	}

}

