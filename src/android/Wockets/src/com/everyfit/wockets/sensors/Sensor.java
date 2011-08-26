/**
 * 
 */
package com.everyfit.wockets.sensors;

import android.app.AlarmManager;
import android.util.Log;
import com.everyfit.wockets.receivers.Receiver;
import com.everyfit.wockets.decoders.Decoder;
import com.everyfit.wockets.decoders.WocketDecoder;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.TimeZone;

import com.everyfit.wockets.data.AccelerationData;
import com.everyfit.wockets.data.WocketData;
import java.util.SimpleTimeZone;

/**
 * @author albinali
 *
 */
public abstract class Sensor {

	public Receiver _Receiver=null;
	public Decoder _Decoder=null;
	public int _ID;
	public int _ReceivedPDUs=0;
	public String _StoragePath="";
	public String _Class;
	/**
	 * 
	 */
	public Sensor(int id,String storagePath) {
		// TODO Auto-generated constructor stub
		_ID=id;
		this._StoragePath=storagePath;
		data=new WocketData(id);
	}
	
	public int Read(){		 
		int numRead = 0;
    	try{           
            int tail = this._Receiver._Buffer._Tail;
            int head = this._Receiver._Buffer._Head;            
            int dataLength = tail - head; 
            if (dataLength < 0)
                dataLength = this._Receiver._Buffer._Bytes.length - head + tail;

            if (dataLength > 0){
            	numRead = this._Decoder.Decode(this._ID, this._Receiver._Buffer, head, tail);
            	this._Receiver._Buffer._Head = tail;
            	this._ReceivedPDUs += numRead;
            }
            
    	}catch(Exception e){
    		 //Log.e(TAG, e.getMessage());
    	}
    	return numRead;
	}
	
	
	public abstract void Reconnect();

	public void Dispose()
	{
		this._Receiver.Dispose();
		this._Decoder.Dispose();
	}

	

	
	// Variables for writing files out:
	private static final String FILE_TYPE_PREFIX = "WocketsAccelBytes";
	private static final String FILE_EXT = "PLFormat";
	private static final int TIMESTAMP_AFTER_SAMPLES = 200;
	private SimpleDateFormat _DateFormat_dayDirectory = new SimpleDateFormat("yyyy-MM-dd");
	private SimpleDateFormat _DateFormat_filename = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-SSS");
	private String currentDataFile;
	private FileOutputStream bw=null;
	private Boolean isForceTimestampSave = true;
	private Boolean _Saving = true;
	private long aUnixTime    = (System.currentTimeMillis()-(AlarmManager.INTERVAL_HOUR*5));
	//private long aUnixTime = System.currentTimeMillis();	
	private long lastUnixTime = aUnixTime;
	private int presentHour = -1;
	private int timeSaveCount = 0;
	private static final String tag = "wocket";
	private String dayPath = "";
	AccelerationData data = null;
	private int tail = 0;    
    public int _SavedPackets = 0; 
    public boolean _Flush=false;
	public void Save() {
		
		
        if (_Saving)
        {     
            int currentHead = -1;
            currentHead = this._Decoder._Head;
        
            //long nowms=(System.currentTimeMillis()-(AlarmManager.INTERVAL_HOUR*5));
            //long nowms = System.currentTimeMillis();
            //Calendar now = Calendar.getInstance(new SimpleTimeZone(0, "GMT"));
            //Calendar now = Calendar.getInstance();
            //now.setTimeInMillis(nowms);
            
            Calendar now = Calendar.getInstance();
        	now.setTimeInMillis(System.currentTimeMillis());
        	TimeZone tz = TimeZone.getDefault();                        	
        	long offset = tz.getOffset(now.getTimeInMillis());
        	long ts = now.getTimeInMillis() + offset;
        	Calendar newnow = Calendar.getInstance();
        	newnow.setTimeInMillis(ts);
            String datetime = _DateFormat_filename.format(newnow.getTime());
        	
            DecimalFormat twoPlaces = new DecimalFormat("00");
            int nowHour=now.get(Calendar.HOUR_OF_DAY);           
            
            if (presentHour != nowHour) 
            {
                if (bw != null)
                {
                	try {
                		bw.flush();
                		bw.close();
                	} catch (Exception e) {
        				
        			}      
                }
                presentHour = nowHour;
                // Need to create a new directory and switch the file name
                dayPath =  this._StoragePath+"data/raw/PLFormat/" + _DateFormat_dayDirectory.format(now.getTime());
                // Make sure hour directory exists 
                currentDataFile = dayPath +  "/" + now.get(Calendar.HOUR_OF_DAY) + "/";
                
            	File directory = new File(currentDataFile);
    			if( !directory.isDirectory() )
    				if( !directory.mkdirs() )
    					Log.e(tag, "Error unable to create direcotry: " + currentDataFile );
    			
    			currentDataFile = currentDataFile + FILE_TYPE_PREFIX + "." + 
				_DateFormat_filename.format(now.getTime()) + "." + this._ID + "." + FILE_EXT;


    			try 
    			{
    				bw = new FileOutputStream(currentDataFile,true);
    			} 
    			catch (FileNotFoundException e) 
    			{
    				presentHour = -1;
    				Log.e(tag, "Unable to open output file: " + currentDataFile );
    			}
                // Ensure that the first data point in the new file will start
                // with the full, rather than differential, timecode info. 
                isForceTimestampSave = true;
            }
           


            // Write data as long as the tail is not equal to the head
            while (tail != currentHead)
            {                   
                data = ((AccelerationData)this._Decoder._Data[tail]);
                
                aUnixTime = data._UnixTimeStamp;
                if (aUnixTime < lastUnixTime)
                {
                    lastUnixTime = aUnixTime;
                    //Log.("Accelerometer: Save: Data overwritten without saving Accelerometer.cs Save " + this._ID + " " + aUnixTime + " " + lastUnixTime);                        
                }                

                if (bw != null)
                {                        
                    diffMS = (int)(aUnixTime - lastUnixTime);
                    if (isForceTimestampSave || (diffMS > 254) || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
                    {
                    
                    	try{
                        bw.write((byte)255);
                    	} catch (IOException e) {
                			// TODO Auto-generated catch block
                			e.printStackTrace();
                		}
                    	int sec = (int)(data._UnixTimeStamp/1000);
                    	short ms= (short)(data._UnixTimeStamp%1000);
                    	
                    	// This gets written out in little endian to be compatible with PL Format:
                    	// TODO: auto swapping based on system endianess
                    	try {
                			bw.write(new byte[] {
                    				(byte)(sec&0xFF),
                			        (byte)((sec >>> 8)&0xFF),
                			        (byte)((sec >>> 16)&0xFF),
                			        (byte)((sec >>> 24)&0xFF) },0,4);
                	    	bw.write(new byte[] {
                	    			(byte)(ms&0xFF),
                    				(byte)((ms >>> 8)&0xFF)},0,2);
                		} catch (IOException e) {
                			// TODO Auto-generated catch block
                			e.printStackTrace();
                		}                        
                        timeSaveCount = 0;
                        isForceTimestampSave = false;
                    }
                    else
                    {
                    	try{
                        bw.write((byte)diffMS);
                    	} catch (IOException e) {
                			// TODO Auto-generated catch block
                			e.printStackTrace();
                		}
                        timeSaveCount++;
                    }
                    

                    for (int j = 0; j < data._Length; j++)
                    {
                    	try{
                    		bw.write(data._RawBytes[j]);
                    	} catch (IOException e) {
                			// TODO Auto-generated catch block
                			e.printStackTrace();
                		}
                    }
                                          
                }
                           
                lastUnixTime = aUnixTime;                
                if (tail >= this._Decoder._Data.length- 1)                    
                    tail = 0;                    
                else
                    tail++;
                this._SavedPackets++;

            }

            if ((bw != null) && (this._Flush)){
            	try{
                bw.flush();
            	} catch (IOException e) {
        			// TODO Auto-generated catch block
        			e.printStackTrace();
        		}
            }            
        }
	}
	
	
	private int diffMS = 0;   
}
