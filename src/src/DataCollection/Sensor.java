/**
 * 
 */
package DataCollection;

//import android.app.AlarmManager;
//import android.util.Log;


import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.TimeZone;
//import java.util.logging.*;

import wockets.data.AccelerationData;
import wockets.data.WocketData;
import wockets.utils.WocketsTimer;

/**
 * @author albinali
 *
 */
public abstract class Sensor {
	private static final String TAG = "SENSOR";
	public Receiver _Receiver=null;
	public Decoder _Decoder=null;
	public int _ID;
	public int _ReceivedPDUs=0;
	public String _StoragePath="";
	public String _Class;	
	public int _SamplingRate;	
	
	public Sensor(int id,String storagePath) {
		// TODO Auto-generated constructor stub
		_ID=id;
		this._StoragePath=storagePath;
		data=new WocketData(id);
	}
	
	public void Initialize()
	{
		this._Receiver.Initialize();
		this._Decoder.Initialize();
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
            
    	}
    	catch(Exception e)
    	{
    		String strMsg = TAG + ":Read()\n";
			strMsg += e.getMessage() + "\n";
			
			StringWriter errTrace = new StringWriter();
			e.printStackTrace(new PrintWriter(errTrace));
			
			strMsg += errTrace.toString();
			
			Logger.error(strMsg);
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
	private SimpleDateFormat _DateFormat_log = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss");
	private String currentDataFile;
	private FileOutputStream bw=null;
	private Boolean isForceTimestampSave = true;
	private Boolean _Saving = true;
	//private long aUnixTime    = (System.currentTimeMillis()-(AlarmManager.INTERVAL_HOUR*5));
	private long aUnixTime = System.currentTimeMillis()- (3600000*5);	
	private long lastUnixTime = aUnixTime;
	private int presentHour = -1;
	private int timeSaveCount = 0;	
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
            
            Calendar now = Calendar.getInstance();
        	now.setTimeInMillis(System.currentTimeMillis());
        	TimeZone tz = TimeZone.getDefault();                        	
        	long offset = tz.getOffset(now.getTimeInMillis());
        	long ts = now.getTimeInMillis() + offset;
        	Calendar newnow = Calendar.getInstance();
        	newnow.setTimeInMillis(ts);
        	            
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
    					//Log.e(TAG, "Error unable to create direcotry: " + currentDataFile );
    					System.out.println(TAG+ "Error unable to create direcotry: " + currentDataFile);
    			
    			currentDataFile = currentDataFile + FILE_TYPE_PREFIX + "." + 
				_DateFormat_filename.format(now.getTime()) + "." + this._ID + "." + FILE_EXT;


    			try 
    			{
    				bw = new FileOutputStream(currentDataFile,true);
    			} 
    			catch (FileNotFoundException e) 
    			{
    				presentHour = -1;
    				//Log.e(TAG, "Unable to open output file: " + currentDataFile );
    				System.out.println(TAG+ "Error unable to create direcotry: " + currentDataFile);
    				
    				String strMsg = TAG + ":Save()\n";
    				strMsg += "Unable to open output file:" + currentDataFile;
					strMsg += e.getMessage() + "\n";
					
					StringWriter errTrace = new StringWriter();
					e.printStackTrace(new PrintWriter(errTrace));
					
					strMsg += errTrace.toString();
					
					Logger.error(strMsg);
    			}
                // Ensure that the first data point in the new file will start
                // with the full, rather than differential, timecode info. 
                isForceTimestampSave = true;
            }
           


            // Write data as long as the tail is not equal to the head
            while (tail != currentHead)
            {                   
                data = ((AccelerationData)this._Decoder._Data[tail]);
                
                Calendar logDt = WocketsTimer.DateTimeFromUnixTime(data._UnixTimeStamp);
                Date logTmpDt = logDt.getTime();                
                
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
                    	} 
                    	catch (IOException e) 
                    	{                			                			                	
            				
            				String strMsg = TAG + ":Save()\n";
            				strMsg += "Unable to write to  output file:" + currentDataFile;
        					strMsg += e.getMessage() + "\n";
        					
        					StringWriter errTrace = new StringWriter();
        					e.printStackTrace(new PrintWriter(errTrace));
        					
        					strMsg += errTrace.toString();
        					
        					Logger.error(strMsg);
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
                		} 
                    	catch (IOException e) 
                		{
                			String strMsg = TAG + ":Save()\n";
            				strMsg += "Unable to write to  output file:" + currentDataFile;
        					strMsg += e.getMessage() + "\n";
        					
        					StringWriter errTrace = new StringWriter();
        					e.printStackTrace(new PrintWriter(errTrace));
        					
        					strMsg += errTrace.toString();
        					
        					Logger.error(strMsg);
                		}                        
                        timeSaveCount = 0;
                        isForceTimestampSave = false;
                    }
                    else
                    {
                    	try{
                        bw.write((byte)diffMS);
                    	} 
                    	catch (IOException e) 
                    	{
                    		String strMsg = TAG + ":Save()\n";
            				strMsg += "Unable to write to  output file:" + currentDataFile;
        					strMsg += e.getMessage() + "\n";
        					
        					StringWriter errTrace = new StringWriter();
        					e.printStackTrace(new PrintWriter(errTrace));
        					
        					strMsg += errTrace.toString();
        					
        					Logger.error(strMsg);
                		}
                        timeSaveCount++;
                    }
                    

                    for (int j = 0; j < data._Length; j++)
                    {
                    	try
                    	{
                    		bw.write(data._RawBytes[j]);
                    	} 
                    	catch (IOException e) 
                    	{
                    		String strMsg = TAG + ":Save()\n";
            				strMsg += "Unable to write to  output file:" + currentDataFile;
        					strMsg += e.getMessage() + "\n";
        					
        					StringWriter errTrace = new StringWriter();
        					e.printStackTrace(new PrintWriter(errTrace));
        					
        					strMsg += errTrace.toString();
        					
        					Logger.error(strMsg);
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
            	try
            	{
            		bw.flush();
            	} 
            	catch (IOException e) 
            	{
            		String strMsg = TAG + ":Save()\n";
    				strMsg += "Unable to flush output file:" + currentDataFile;
					strMsg += e.getMessage() + "\n";
					
					StringWriter errTrace = new StringWriter();
					e.printStackTrace(new PrintWriter(errTrace));
					
					strMsg += errTrace.toString();
					
					Logger.error(strMsg);
        		}
            }            
        }
	}
	
	
	private int diffMS = 0;   
	
	//Variables for reading data
	public ArrayList<String> someBinaryFiles = new ArrayList<String>();
	private FileInputStream br;
	private boolean loading = false;
	private int fileIndex = 0;
	
	public class PLFormatFilter implements FilenameFilter
	{
		private final String FILE_TYPE_PREFIX = "WocketsAccelBytes";
		private final String FILE_EXT = "PLFormat";
				
		public boolean accept(File dir, String filename) 
		{			
			if(filename.startsWith(FILE_TYPE_PREFIX) && filename.endsWith(FILE_EXT))
				return true;
			else
				return false;
		}
		
	}
	
	private void GenerateBinaryFileList()
	{	
		FilenameFilter filter = new PLFormatFilter();
		File storagePath = new File(this._StoragePath);		
		if(storagePath.isDirectory() == false)
			return;
		
		File[] subDirectories = storagePath.listFiles();
		for(File file : subDirectories)
		{
			for(int i = 0 ; i < 30 ; i++)
			{
				File subDir = new File(file + "/" + i);
				if(subDir.isDirectory())
				{
					File[] matchingFiles = subDir.listFiles(filter);
					
					for(int j = 0 ; j < matchingFiles.length; j++)
					{
						someBinaryFiles.add(matchingFiles[j].getPath());
					}
				}
			}
		}
	}
	
	private boolean SetupNextFiles(int index)
	{
		if(br != null)
		{
			try 
			{
				br.close();
			} 
			catch (IOException e1)
			{			
				String strMsg = TAG + ":SetupNextFiles()\n";
				
				strMsg += e1.getMessage() + "\n";
				
				StringWriter errTrace = new StringWriter();
				e1.printStackTrace(new PrintWriter(errTrace));
				
				strMsg += errTrace.toString();
				
				Logger.error(strMsg);
			}

		}
					
		br = null;
		
		String f = ((String)someBinaryFiles.get(index));
		
		if(f != "")
		{
			try 
			{
				br = new FileInputStream(f);
			}
			catch (FileNotFoundException e) 
			{
				String strMsg = TAG + ":SetupNextFiles()\n";
				
				strMsg += e.getMessage() + "\n";
				
				StringWriter errTrace = new StringWriter();
				e.printStackTrace(new PrintWriter(errTrace));
				
				strMsg += errTrace.toString();
				
				Logger.error(strMsg);
			}			
		}
		if(br == null)
			return false;
		else
			return true;
	}
	
	public boolean Load()
	{
		if(loading == false)
		{
			GenerateBinaryFileList();
			if(someBinaryFiles.size() < 1)
				return false;
			SetupNextFiles(0);
			loading = true;
		}
		while(loading)
		{
			try
			{
				this._Decoder.Load(br);
				//return true;
				loading = true;
				break;
			}
			catch(Exception ex)
			{
				String strMsg = TAG + ":Load()\n";
				
				strMsg += ex.getMessage() + "\n";
				
				StringWriter errTrace = new StringWriter();
				ex.printStackTrace(new PrintWriter(errTrace));
				
				strMsg += errTrace.toString();
				
				Logger.error(strMsg);
				try 
				{
					br.close();
				}
				catch (IOException e)
				{
					String strMsg1 = TAG + ":SetupNextFiles()\n";
					strMsg1 += "Unable to close file \n";
					strMsg1 += e.getMessage() + "\n";
					
					StringWriter errTrace1 = new StringWriter();
					e.printStackTrace(new PrintWriter(errTrace1));
					
					strMsg1 += errTrace1.toString();
					
					Logger.error(strMsg1);
				}				
				if (!((++fileIndex < someBinaryFiles.size()) && SetupNextFiles(fileIndex)))
				{
					loading = false;
					break;									
				}						
			}
		}
		return loading;
	}
}
