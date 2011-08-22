package com.everyfit.wockets.sensors;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.TimeZone;

import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.util.Log;
import com.everyfit.wockets.decoders.AndroidDecoder;
import com.everyfit.wockets.receivers.AndroidReceiver;

public class AndroidSensor extends Sensor
{
	protected static final String TAG = "AndroidSensor";
	public float mAccelRange;
    public float mAccelResolution;
    public float mAccelBits;
    public float mAccelNorm;
    public ArrayList<float[]> mRawData;		
	private long mSensorTimeStamp;
	private int mSensorX;
	private int mSensorY;
	private int mSensorZ;
	public int mPrevSensorX;
	public int mPrevSensorY;
	public int mPrevSensorZ;
//	private int myX;
//	private int myY;
//	private int myZ;
	
	short diffX;
	short diffY;
	short diffZ;
	
	int diffSignX;
	int diffSignY;
	int diffSignZ;
	
	byte[] out;
	int noBits = 0;
	
	byte prevByte = 0;
	byte currByte;
	byte temp;
	
	private SimpleDateFormat _DateFormat_filename = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-SSS");
	private SimpleDateFormat _DateFormat_dayDirectory = new SimpleDateFormat("yyyy-MM-dd");
	String currentDataFile = null;
	private int presentHour = -1;
	private FileOutputStream bw = null;
//	BufferedWriter bw = null;
	private String dayPath ="";
	private Boolean isForceTimeStamp = true;
	private String _FILE_TYPE_PREFIX = "PhoneAccelBytes";
	String _FILE_EXT = "baf";
	//private int _ID = 0;
	private long aUnixTime;
	private long lastUnixTime;
	private int diffMS;
	private int timeSaveCount;
	private final int TIMESTAMP_AFTER_SAMPLES = 200;

	public SensorEventListener mSensorEventListener = new SensorEventListener() 
	{	
	
		public void onSensorChanged(SensorEvent event)
		{
			if(event.sensor.getType() != android.hardware.Sensor.TYPE_ACCELEROMETER)
				return;
			else
			{								
				mRawData.add(event.values.clone());				
				mSensorTimeStamp = System.currentTimeMillis();
											
				// Preparing the output directory and output file for the raw data
								
				Calendar now = Calendar.getInstance();
				now.setTimeInMillis(System.currentTimeMillis());
				TimeZone tz = TimeZone.getDefault();
				long offset = tz.getOffset(now.getTimeInMillis());
				long ts = now.getTimeInMillis() + offset;
				Calendar newnow = Calendar.getInstance();
				newnow.setTimeInMillis(ts);
				_DateFormat_filename.format(now.getTime());				
				
				int nowHour = now.get(Calendar.HOUR_OF_DAY);
				
				if(presentHour != nowHour)
				{
					if(bw != null)
					{
						try
						{
							bw.flush();
							bw.close();
						}
						catch(Exception ex)
						{
							Log.e(TAG,"Exception while flushing data");
						}
					}
					presentHour = nowHour;
					dayPath = _StoragePath + "data/raw/PLFormat/" + _DateFormat_dayDirectory.format(newnow.getTime());
					currentDataFile = dayPath + "/" + now.get(Calendar.HOUR_OF_DAY) + "/";
					
					File directory = new File(currentDataFile);
					if(!directory.isDirectory())
						if(!directory.mkdirs())
							Log.e(TAG,"Unable to create directory:" + currentDataFile);
					
					currentDataFile = currentDataFile + _FILE_TYPE_PREFIX + "." + 
					_DateFormat_filename.format(now.getTime()) + "." + _ID + "." + _FILE_EXT;
					
					
					try
					{
						bw = new FileOutputStream(currentDataFile,true)	;
						//bw = new BufferedWriter(new FileWriter(currentDataFile, true));
					}
					catch(Exception ex)
					{
						Log.e(TAG,"Unable to open output file:" + currentDataFile);
					}
					
					//Ensure that the first data point in the new file will start with the full timestamp
					isForceTimeStamp = true;
				}
				mSensorX = (int) ((mAccelRange + event.values[0]) / mAccelNorm);
				mSensorY = (int) ((mAccelRange + event.values[1]) / mAccelNorm);
				mSensorZ = (int) ((mAccelRange + event.values[2]) / mAccelNorm);
				
//				myX = (int) ((mAccelRange + event.values[0]) / mAccelNorm);
//				myY = (int) ((mAccelRange + event.values[1]) / mAccelNorm);
//				myZ = (int) ((mAccelRange + event.values[2]) / mAccelNorm);
				
				 aUnixTime = mSensorTimeStamp;
				if(aUnixTime < lastUnixTime)
					lastUnixTime = aUnixTime;
				
				//write the data to the current output file
				if(bw != null)
				{
					//write the timestamp
					diffMS = (int)(aUnixTime - lastUnixTime);
					if(isForceTimeStamp || (diffMS > 254) || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
					{					
						try
						{
							bw.write((byte)255);
						}
						catch(IOException ex)
						{
							Log.e(TAG,"Exception while writing raw data to :" + currentDataFile);
						}
						int sec = (int)(aUnixTime/1000);
						short ms = (short)(aUnixTime%1000);
						
						try
						{													
							bw.write(new byte[] {
                    				(byte)(sec&0xFF),
                			        (byte)((sec >>> 8)&0xFF),
                			        (byte)((sec >>> 16)&0xFF),
                			        (byte)((sec >>> 24)&0xFF) },0,4);
                	    	bw.write(new byte[] {
                	    			(byte)(ms&0xFF),
                    				(byte)((ms >>> 8)&0xFF)},0,2);
						}
						catch(IOException ex)
						{
							Log.e(TAG,"Exception while writing raw data to :" + currentDataFile);
						}
						timeSaveCount = 0;
						isForceTimeStamp = false;
					}
					else
					{
						
						try
						{
							bw.write((byte)diffMS);
						}
						catch(IOException ex)
						{
							Log.e(TAG,"Exception while writing raw data to :" + currentDataFile);
						}
						timeSaveCount++;
					}					
					
					//write the raw accelerometer data
					// calculate difference for x-axis,y-axis and z-axis
					diffX = (short) (mSensorX - mPrevSensorX) ;
					diffY = (short) (mSensorY - mPrevSensorY);
					diffZ = (short) (mSensorZ -  mPrevSensorZ);
					
					if(diffX < 0)
						diffSignX = 1;
					else 
						diffSignX = 0;
					if(diffY < 0)
						diffSignY = 1;
					else 
						diffSignY = 0;
					if(diffZ < 0)
						diffSignZ = 1;
					else 
						diffSignZ = 0;
					
					//compress based on difference between current and previous value
					//fully compressed
					if( (diffX > -3) && (diffX < 4) && (diffY > -3) && (diffY < 4) && (diffZ > -3) && (diffZ < 4))
					{
						diffX = (short) Math.abs(diffX);
						diffY = (short) Math.abs(diffY);
						diffZ = (short) Math.abs(diffZ);
						
						switch(noBits)
						{
							case 0 :
							{
								diffX = (byte)diffX;
								currByte = (byte) (((byte)(diffX << 4)) | ((byte)(diffSignX << 6)));
								currByte |= (byte)(diffSignY << 3);
								currByte |= (byte)(diffY << 1);
								currByte |= (byte)(diffSignZ);
									
								////System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte)(diffZ << 6);
								prevByte = currByte;
								noBits = 2;
								break;
							}
							case 1:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)diffSignX << 5);
								currByte |= (byte) ((byte)diffX << 3);
								currByte |= (byte) ((byte)diffSignY << 2);
								currByte |= (byte) ((byte)diffY);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								
								currByte = (byte) ((byte)diffSignZ << 7);
								currByte |= (byte) ((byte)diffZ << 5);
								prevByte = currByte;
								noBits = 3;
								break;
							}
							case 2:
							{
								currByte = prevByte;
								currByte |= (byte)((byte) diffSignX << 4);
								currByte |= (byte)(((byte)diffX) << 2);
								currByte |= (byte) ((byte)diffSignY << 1);														
								currByte |= (byte) (diffY >>> 1);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte)((byte)(diffY & 0x01) << 7);
								currByte |= (byte)(((byte)diffSignZ) << 6);
								currByte |= (byte) (diffZ << 4);
								prevByte = currByte;
								noBits = 4;
								break;
							}
							case 3:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)diffSignX << 3);
								currByte |= (byte) ((byte)diffX << 1);
								currByte |= (byte) ((byte)diffSignY);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte) diffY << 6);
								currByte |= (byte) ((byte)diffSignZ << 5);
								currByte |= (byte) ((byte)diffZ << 3);
								prevByte = currByte;
								noBits = 5;
								break;
							}
							case 4:
							{
								currByte = prevByte;
								currByte |= (byte)((byte) diffSignX << 2);
								currByte |= (byte)((byte) diffX);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte)((byte)diffSignY << 7);
								currByte |= (byte)((byte)diffY << 5);
								currByte |= (byte)((byte)diffSignZ << 4);
								currByte |= (byte)((byte)diffZ << 2);
								prevByte = currByte;
								noBits = 6;
								break;
							}
							case 5:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)diffSignX << 1);
								currByte |= (byte) (((byte)diffX)>>> 1);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}	
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) (((byte) diffX) & 0x01);
								currByte |= (byte) ((byte)diffSignY << 6);
								currByte |= (byte) ((byte)diffY << 4);
								currByte |= (byte) ((byte)diffSignZ << 3);
								currByte |= (byte) ((byte)diffZ << 1);
								prevByte = currByte;
								noBits = 7;
								break;
							}
							case 6:
							{
								currByte = prevByte;
								currByte |= (byte)((byte)diffSignX);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte)((byte)diffX << 6);
								currByte |= (byte) ((byte)diffSignY << 5);
								currByte |= (byte) ((byte)diffY << 3);
								currByte |= (byte) ((byte)diffSignZ << 2);
								currByte |= (byte) ((byte)diffZ);
								prevByte = currByte;
								noBits = 0;
								break;
							}
							case 7:
							{
								currByte = prevByte;
								currByte |= 0x00;
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffSignX << 7);
								currByte |= (byte) ((byte)diffX << 5);
								currByte |= (byte) ((byte)diffSignY << 4);
								currByte |= (byte) ((byte)diffY << 2);
								currByte |= (byte) ((byte)diffSignZ << 1);
								currByte |= (byte) (((byte)diffZ) >>> 1);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) (((byte)diffZ & 0x01) << 7);
								prevByte = currByte;
								noBits =1;
								break;
							}
						}
						
					}
					//moderately compressed
					else if(diffX < 32 && diffY < 32 && diffZ < 32 && diffX > -31 && diffY > -31 && diffZ > -31)
					{
						diffX = (short) Math.abs(diffX);
						diffY = (short) Math.abs(diffY);
						diffZ = (short) Math.abs(diffZ);
						
						switch(noBits)
						{
							case 0:
							{							
								currByte = (byte) ( (byte)0x02 << 6);
								//System.out.println(((byte)currByte));
								currByte |= (byte) ((byte)diffSignX << 5);
								//System.out.println(((byte)currByte));
								currByte |= (byte) ((byte)diffX);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffSignY << 7);
								currByte |= (byte) ((byte)diffY << 2);
								currByte |= (byte) ((byte)diffSignZ << 1);
								currByte |= (byte) ((byte)diffZ >>> 4);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffZ << 4);
								prevByte = currByte;
								noBits = 4;
								break;
							}
							case 1:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte) 0x02 << 5);
								currByte |= (byte) ((byte) diffSignX << 4);
								currByte |= (byte)  ((byte) diffX >>> 1);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffX << 7);
								currByte |= (byte) ((byte)diffSignY << 6);
								currByte |= (byte) ((byte)diffY << 1);
								currByte |= (byte) ((byte)diffSignZ);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffZ << 3);
								prevByte = currByte;
								noBits = 5;
								break;
							}
							case 2:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)0x02 << 4);
								currByte |= (byte) ((byte)diffSignX << 3);
								currByte |= (byte) ((byte)diffX >>> 2 );
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								//System.out.println(((byte)currByte));
								currByte = (byte) ((byte)diffX << 6);
								currByte |= (byte) ((byte)diffSignY << 5);
								currByte |= (byte) ((byte)diffY);
								
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								//System.out.println(((byte)currByte));
								currByte = (byte) ((byte)diffSignZ << 7);
								currByte |= (byte) ((byte)diffZ << 2);
								prevByte = currByte;
								noBits = 6;
								break;
							}
							case 3:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)0x02 << 3);
								currByte |= (byte) ((byte)diffSignX << 3);
								currByte |= (byte) ((byte)diffX >>> 3);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffX << 5);
								currByte |= (byte) ((byte)diffSignY << 4);
								currByte |= (byte) ((byte)diffY >>> 1);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								//System.out.println(((byte)currByte));
								currByte = (byte) ((byte)diffY << 7);
								currByte |= (byte) ((byte)diffSignZ << 6);
								currByte |= (byte) ((byte)diffZ << 1);
								prevByte = currByte;
								noBits = 7;
								break;
							}
							case 4:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)0x02 << 2);
								currByte |= (byte) ((byte)diffSignX << 1);
								currByte |= (byte) ((byte)diffX >>> 4);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffX << 4);
								currByte |= (byte) ((byte)diffSignY << 3);
								currByte |= (byte) ((byte)diffY >>> 2);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffY << 6);
								currByte |= (byte) ((byte)diffSignZ << 5);
								currByte |= (byte) ((byte)diffZ);
								//System.out.println(((byte)currByte));
								
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								noBits = 0;
								break;
							}
							case 5:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)0x02 << 1);
								currByte |= (byte) ((byte)diffSignX);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffX << 3);
								currByte |= (byte) ((byte)diffSignY << 2);
								currByte |= (byte) ((byte)diffY >>> 3);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffY << 5);
								currByte |= (byte) ((byte)diffSignZ << 4);
								currByte |= (byte) ((byte)diffZ >>> 1);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffZ << 7);
								prevByte = currByte;
								noBits = 1;
								break;
							}
							case 6:
							{
								currByte = prevByte;
								currByte |= (byte) ((byte)0x02);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffSignX << 7);
								currByte |= (byte) ((byte)diffX << 2);
								currByte |= (byte) ((byte)diffSignY << 1);
								currByte |= (byte) ((byte)diffY >>> 4);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffY << 4);
								currByte |= (byte) ((byte)diffSignZ << 3);
								currByte |= (byte) ((byte)diffZ >>> 2);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffZ << 6);
								prevByte = currByte;
								noBits = 2;
								break;
							}
							case 7:
							{
								currByte = prevByte;
								currByte |= (byte)((byte)0x01);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffSignX >> 6);
								currByte |= (byte) ((byte)diffX << 1);
								currByte |= (byte) ((byte)diffSignY);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffY << 3);
								currByte = (byte) ((byte)diffSignZ << 2);
								currByte = (byte) ((byte)diffZ >>> 3);
								//System.out.println(((byte)currByte));
								try
								{
									bw.write(currByte);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								currByte = (byte) ((byte)diffZ << 5);
								prevByte = currByte;
								noBits = 3;
								break;
								
							}
						}
					}
					//uncompressed
					else 
					{
						diffX = (short) mSensorX;
						diffY = (short) mSensorY;
						diffZ = (short) mSensorZ;
						switch(noBits)
						{
							case 0:
							{
								out = new byte[4];
								
								currByte = (byte) ((byte)(0x03) << 6);
								//bits 1-2 for diffX
								temp = (byte) ((diffX >>> 8) &0xFF);
								currByte |= (byte) ((temp << 4));
								//bits 3-10
								temp = (byte) (diffX &0xFF);							
								currByte |= (byte) (temp >>> 4);//bits 3-6							
								out[0] = currByte;
															
								currByte = (byte) ((byte)(temp << 4));//bits 7-10 for diffX
								temp = (byte) ((diffY >>> 8 ) & 0xFF); //bits 1-2 for diffY
								currByte |= (byte)(temp << 4);
								temp = (byte)(diffY & 0xFF);// bits 3-10
								currByte |= (byte) (temp >>> 6 ); //bits 3-4 for diffY
								out[1] = currByte;
								
								
								currByte = (byte)(temp << 2);// bits 5-10 for diffY
								temp = (byte) ((diffZ >>> 8) & 0xFF); // bits 1-2 for diffZ
								currByte |= (byte) (temp);
								out[2] = currByte;
								
															
								temp = (byte) (diffZ & 0xFF); //bits 3-10 for diffZ
								currByte = (byte) (temp);
								out[3] = currByte;
								
								noBits = 0;
								
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}																			
								
								break;																											
							}
							case 1:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte) (0x03 << 5);
								temp = (byte)((diffX >>> 8) & 0xFF);//bits 1-2 for diffX
								currByte |= (byte) (temp << 3);
								temp = (byte) (diffX & 0xFF);// bits 3-10 for diffX
								currByte |= (byte) (temp >>> 5);// bits 3-5 for diffX
								out[0] = currByte;
								
								currByte = (byte)(temp << 3);//bits 6-10 for diffX
								temp = (byte) ((diffY >>> 8) & 0xFF);// bits 1-2 for diffY
								currByte |= (byte) (temp >>> 5); // bit 3 for diffY
								out[1] = currByte;
								
								currByte = (byte) (temp << 3);// bits 4-10 for diffY
								temp = (byte) ((diffZ >>8) & 0xFF); // bits 1-2 for diffZ
								currByte |= (byte) (temp >> 1);//bit 1 for diffZ
								out[2] = currByte;
								
								currByte = (byte) (temp << 7);//bit 2 for diffZ
								temp = (byte)(diffZ & 0xFF); //bits 3-10 for diffZ
								currByte |= (byte) (temp >>> 1); // bits 3-9 for diffZ
								out[3] = currByte;

								currByte = (byte) (temp << 7);//bit 10 for diffZ
								prevByte = currByte;
								noBits = 1;
											
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
												
								break;
							}
							case 2:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte) (0x03 << 4);
								temp = (byte) ((diffX >>> 8) & 0xFF);//bits 1-2 for diffX
								currByte |= (byte)(temp << 2);
								temp = (byte) (diffX & 0xFF);//bits 3-10 for diffX
								currByte |= (byte) (temp >>> 6);//bits 3-4
								out[0] = currByte;
								
								currByte = (byte)(temp << 2);//bits 5-10
								temp = (byte) ((diffY >>> 8) & 0xFF);//bits 1-2 for diffY
								currByte |= (byte)temp;
								out[1] = currByte;
								
								temp = (byte) (diffY & 0xFF);//bits 3-10 for diffY
								currByte = (byte)temp;
								out[2] = currByte;
								
								temp = (byte)((diffZ >>> 8) & 0xFF);//bits 1-2 for diffZ
								currByte = (byte) (temp << 6);
								temp = (byte)(diffZ & 0xFF);//bits 3-10 for diffZ
								currByte |= (byte) (temp >>> 2); //bits 3-8 for diffZ
								out[3] = currByte;

								currByte = (byte)(temp << 6);
								prevByte = currByte;
								noBits = 2;							

								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
																					
								break;
							}
							case 3:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte)(0x03 << 3);
								temp = (byte)((diffX >>> 8) & 0xFF);//bits 1-2 for diffX
								currByte |= (byte)(temp << 1);
								temp = (byte) (diffX & 0xFF);// bits 3-10 for diffX
								currByte = (byte) (temp >>> 7);// bit 3 for diffX
								out[0] = currByte;
								
								currByte = (byte)(temp << 1);//bits 4-10 for diffX
								temp = (byte) ((diffY >>> 8) & 0xFF);//bits 1-2 for diffY
								currByte |= (byte) (temp >>> 1);//bit 1 for diffY
								out[1] = currByte;
								
								currByte = (byte)(temp << 7);// bit 2 for diffY
								temp = (byte) (diffY &0xFF); // bits 3-10 for diffY
								currByte |= (byte) (temp >>> 1); //bits 3-9 for diffY
								out[2] = currByte;
								
								currByte = (byte)(temp << 7);//bit 10 for diffY
								temp = (byte) ((diffZ >>> 8) & 0xff);//bits 1-2 for diffZ
								currByte |= (byte) (temp << 5);
								temp = (byte) (diffZ & 0xFF);// bits 3-10 for diffZ
								currByte |= (byte)(temp >>> 3);//bits 3-7 for diffZ
								out[3] = currByte;
								
								currByte = (byte) (temp << 5);// bits 8-10 for diffZ
								prevByte = currByte;
								noBits = 3;
								
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}														
								
								break;
							}
							case 4:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte) (0x03 << 2);//header bits
								temp = (byte) ((diffX >>> 8) & 0xFF);//bits 1-2 for diffX
								currByte |= (byte)temp;
								out[0] = currByte;
								
								temp = (byte)(diffX & 0xFF);//bits 3-10 for diffX
								currByte = (byte)temp;
								out[1] = currByte;
								
								temp = (byte) ((diffY >>> 8) & 0xFF);//bits 1-2 for diffY
								currByte = (byte)(temp << 6);
								temp = (byte)(diffY & 0xFF);//bits 3-10 for diffY
								currByte |= (byte) (temp >>> 2);//bits 3-8 for diffY
								out[2] = currByte;
								
								currByte = (byte) (temp << 6); // bits 9-10 for diffY
								temp = (byte) ((diffZ >>> 8) & 0xFF);//bits 1-2 for diffZ
								currByte |= (byte)(temp << 4);
								temp = (byte)(diffZ & 0xFF);//bits 3-10 for diffZ
								currByte |= (byte)(temp >>> 4);
								out[3] = currByte;
								
								currByte = (byte)(temp << 4);
								prevByte = currByte;
								noBits = 4;
								
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								break;
							}
							case 5:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte)(0x03 << 1);//header bits
								temp = (byte) ((diffX >>> 8) & 0xFF);//bits 1-2 for diffX
								currByte |= (byte)(temp >>> 1);//bit 1 for diffX
								out[0] = currByte;
								
								currByte = (byte) (temp << 7);//bit 2 for diffX
								temp = (byte) (diffX & 0xFF);//bits 3-10 for diffX
								currByte |= (byte)(temp >>> 1);//bits 3-9 for diffX
								out[1] = currByte;
								
								currByte = (byte)(temp << 7);//bit 10 for diffX
								temp = (byte)((diffY >>> 8) & 0xFF);//bits 1-2 for diffY
								currByte |= (byte)(temp << 5);
								temp = (byte)(diffY & 0xFF);//bits 3-10 for diffY
								currByte |= (byte)(temp >>> 3);//bits 3-7 for diffY
								out[2] = currByte;
								
								currByte = (byte)(temp << 5);//bits 8-10 for diffY
								temp = (byte) ((diffZ >>> 8) & 0xFF);//bits 1-2 for diffZ
								currByte |= (byte)(temp << 3);
								temp = (byte) (diffZ & 0xFF);//bits 3-10 for diffZ
								currByte |= (byte) (temp >>> 5); // bits 3-5 for diffZ
								out[3] = currByte;
								
								currByte = (byte)(temp << 3);//bits 6-10 for diffZ
								prevByte = currByte;
								noBits = 5;
								
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								break;
							}
							case 6:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte)(0x03);//header bits
								out[0] = currByte;
								
								temp = (byte) ((diffX >>> 8) & 0xFF);//bits 1-2 for diffX
								currByte = (byte)(temp << 6);
								temp = (byte) (diffX & 0xFF);//bits 3-10 for diffX
								currByte |= (byte) (temp >>> 2);//bits 3-8 for diffX
								out[1] = currByte;
								
								currByte = (byte) (temp << 6);//bits 9-10 for diffX
								temp = (byte) ((diffY >>> 8) & 0xFF);//bits 1-2 for diffY
								currByte |= (byte) (temp << 4);
								temp = (byte) (diffY & 0xFF);//bits 3- 10 for diffY
								currByte |= (byte)(temp >>> 4);//bits 3-6 for diffY
								out[2] = currByte;
								
								currByte = (byte) (temp << 4);//bits 7-10 for diffY
								temp = (byte)((diffZ >>> 8 )& 0xFF);// bits 1-2 for diffZ
								currByte |= (byte)(temp << 2);
								temp = (byte)(diffZ & 0xFF);//bits 3-10 for diffZ
								currByte |= (byte)(temp >>> 6);//bits 3-4 for diffZ
								out[3] = currByte;
								
								currByte = (byte)(temp << 2);//bits 5-10 for diffZ
								prevByte = currByte;
								noBits = 6;
								
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								break;
							}
							case 7:
							{
								out = new byte[4];
								
								currByte = prevByte;
								currByte |= (byte)(0x03 >>> 1);//header bit
								out[0] = currByte;
								
								currByte = (byte)(0x03 << 7);//header bit
								temp = (byte)((diffX >>> 8 )& 0xFF);//bits 1-2 for diffX
								currByte |= (byte)(temp << 5);
								temp = (byte)(diffX & 0xFF);//bits 3-10 for diffX
								currByte |= (byte)(temp >>> 3);//bits 3-7 for diffX
								out[1] = currByte;
								
								currByte = (byte) (temp << 5);//bits 8-10 for diffX;
								temp = (byte) ((diffY >>> 8) & 0xFF);//bits 1-2 for diffY
								currByte |= (byte) (temp << 3);
								temp = (byte)(diffY & 0xFF);//bits 3-10 for diffY
								currByte |= (byte)(temp >>> 5);//bits 3-5 for diffY
								out[2] = currByte;
								
								currByte = (byte) (temp << 3);//bits 6-10 for diffY
								temp = (byte)((diffZ >>> 8 )& 0xFF);//bits 1-2 for diffZ
								currByte |= (byte) (temp << 1);
								temp = (byte)(diffZ & 0xFF);//bits 3-10 for diffZ
								currByte |= (byte) (temp >>> 7);//bit 3 for diffZ
								out[3] = currByte;
								
								currByte = (byte) (temp << 1);//bits 4-10 for diffZ
								prevByte = currByte;
								noBits = 7;
								
								try
								{
									for(int j = 0 ; j < out.length ; j++)
										bw.write(out[j]);
									bw.flush();
								}
								catch(Exception ex)
								{
									System.out.println(ex.getMessage());
								}
								
								break;
							}
						}
					}					
					
					lastUnixTime = aUnixTime;
					mPrevSensorX = mSensorX;
					mPrevSensorY = mSensorY;
					mPrevSensorZ = mSensorZ;
					
					
					try
					{
						if(bw != null)
							bw.flush();
					}
					catch(Exception ex)
					{
						Log.e(TAG,"Unable to flush output stream :" + currentDataFile);
					}
				}								
			}			
		}
		
	
		public void onAccuracyChanged(android.hardware.Sensor sensor,
				int accuracy) 
		{
			
			
		}
	
	};
	public AndroidSensor(int id, String storagePath) 
	{
		super(id, storagePath);
		this._Class = "Android";
		this._Receiver = new AndroidReceiver(id);
		this._Receiver.Initialize();
		this._Decoder = new AndroidDecoder(id);
		this._Decoder.Initialize();
		this.mRawData = new ArrayList<float[]>();
				 
	}

	@Override
	public void Reconnect() 
	{
		
	}
	
	@Override public void Save()
	{
		
	}
	
	@Override
	public void Dispose()
	{
		if (noBits != 0 && bw != null)
		{
			switch(noBits)
			{
				case 1:
				{
					currByte = prevByte;
					currByte &= (byte) 0x80;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;						
				}
				case 2:
				{
					currByte = prevByte;
					currByte &= (byte) 0xC0;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;
				}
				case 3:
				{
					currByte = prevByte;
					currByte &= (byte) 0xE0;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;
				}
				case 4:
				{
					currByte = prevByte;
					currByte &= (byte) 0xF0;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;
				}
				case 5:
				{
					currByte = prevByte;
					currByte &= (byte) 0xF8;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;
				}
				case 6:
				{
					currByte = prevByte;
					currByte &= (byte) 0xFC;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;
				}
				case 7:
				{
					currByte = prevByte;
					currByte &= (byte) 0xFE;
					
					try
					{
						bw.write(currByte);
						bw.flush();
					}
					catch(Exception ex)
					{
						System.out.println(ex.getMessage());
					}
					break;
				}
			}
			
		}
		super.Dispose();
	}

}
