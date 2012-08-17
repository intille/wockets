package bafFormat;

import java.io.BufferedOutputStream;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.TimeZone;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;


public class BafEncoder {
	private static String localPath;
	private static int previousX;
	private static int previousY;
	private static int previousZ;
	private static long prevTimeStamp;
	private static byte[] data;
	//private static byte[] timeInBytes;
	public final static int FAKE_TIME_DIFF = 1;
	private long ref_time = 0;
	public BafEncoder(){
		resetPrevData();
	}
	/*
	 ******************************************************************************
	 *******************Encoding code for PC or continuous mode********************
	 ******************************************************************************
	*/
	public void encodeAndSaveData(Calendar time, int x, int y, int z, String ID){
		BufferedOutputStream outputStream = null;
		localPath = "c:/test/";
		try {
			long timeStamp = time.getTimeInMillis();
			String outputFilePath = getFilePathByTime(time);
			boolean isNewFile = false;
			File outputDir = new File(outputFilePath);
			if(!outputDir.isDirectory()){
				outputDir.mkdirs();
			}
			String outputFileName = getFileNameForCurrentHour(outputFilePath, time, ID);
			File outputFile = new File(outputFilePath+outputFileName);
			if(!outputFile.exists()){
				outputFile.createNewFile();
				isNewFile = true;
			}
			outputStream = new BufferedOutputStream(new FileOutputStream(outputFile,true));

			if(isNewFile){
				resetPrevData();
			}
			
			FileOutputStream fos = new FileOutputStream(outputFile, true);
			fos.write(encodeTime(timeStamp));
			fos.write(encoRawData( x, y, z));
			fos.flush();
			fos.close();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} finally{
			try {
				if(outputStream != null){
					outputStream.flush();
					outputStream.close();
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	
	//*************************************************************************************************************************************
	private void resetPrevData(){
		previousX = 0;
		previousY = 0;
		previousZ = 0;
		prevTimeStamp = 0;
		//ref_time = 0;
	}
	private byte[] encodeTime(long stamp){
		if ((prevTimeStamp == 0) || (stamp-prevTimeStamp>127) || (stamp-ref_time>60000)){
			ref_time = stamp;
			return encodeFullTimeStamp(stamp);			
		} else{
			return encodeDiffTimeStamp(stamp-prevTimeStamp);
		}
	}
	public byte[] encodeFullTimeStamp(long time){

		byte[] timeInBytes;
		prevTimeStamp = time;
		Calendar timeStamp = Calendar.getInstance();
		timeStamp.setTimeInMillis(time);
		int year = timeStamp.get(Calendar.YEAR);
		int month = timeStamp.get(Calendar.MONTH);
		month++;
		int day = timeStamp.get(Calendar.DAY_OF_MONTH);
		int mills = (int) (timeStamp.get(Calendar.HOUR_OF_DAY)*60*60*1000 + timeStamp.get(Calendar.MINUTE)*60*1000 + timeStamp.get(Calendar.SECOND)*1000 + timeStamp.get(Calendar.MILLISECOND));
		timeInBytes = new byte[8];
		timeInBytes[0] = (byte) ((byte)((year >>> 8))|0x80);
		timeInBytes[1] = (byte)(year);
		timeInBytes[2] = (byte)(month);
		timeInBytes[3] = (byte)(day);
		timeInBytes[4] = (byte)(mills >>> 24);
		timeInBytes[5] = (byte)(mills >>> 16);
		timeInBytes[6] = (byte)(mills >>> 8);
		timeInBytes[7] = (byte)(mills);
		return timeInBytes;
	}
	public byte[] encodeDiffTimeStamp(long diff){
		byte[] timeInBytes;
		prevTimeStamp += diff;
		timeInBytes = new byte[1];
		timeInBytes[0] = (byte)diff;
		return timeInBytes;
	}
	
	public byte[] encoRawData(int x, int y, int z){
		if(previousX == 0 && previousY == 0 && previousZ == 0){
			previousX = x;
			previousY = y;
			previousZ = z;
			uncompressedData(x, y, z);
		}
		else{
			int dx,dy,dz;
			dx=x-previousX;
			dy=y-previousY;
			dz=z-previousZ;
			previousX=x;
			previousY=y;
			previousZ=z;
			if(dx >= -15 && dx <= 15 && dy >= -15 && dy <= 15 && dz >= -15 && dz <= 15){
				compressedData(dx, dy, dz);
			}else
				uncompressedData(x, y, z);
		}
		return data;
	}
	
	private void compressedData(int dx, int dy, int dz){
		data = new byte[2];
		if(dx < 0){
			dx *= -1;
			data[0] = (byte) (((byte) (dx << 2) & 0x3c) | 0x40);
		}
		else
			data[0] = (byte) (((byte) (dx << 2) & 0x3c));
		if(dy < 0){
			dy *= -1;
			data[0] = (byte) (data[0] | 0x02 | ((byte)dy >> 3));
			data[1] = (byte) (dy << 5);
		}
		else{
			data[0] = (byte) (data[0] | ((byte)dy >> 3));
			data[1] = (byte) (dy << 5);
		}
		if(dz < 0){
			dz *= -1;
			data[1] = (byte) (data[1] | 0x10 | (byte)dz);
		}
		else
			data[1] = (byte) (data[1] | (byte)dz);
	}
	
	private void uncompressedData(int x, int y, int z){
		data = new byte[4];
		data[0]=(byte) ((x >>> 4) | 0xc0);
		data[1]=(byte) (((x << 4) & 0xf0) | ((y >>> 6) & 0x0f));
		data[2]=(byte) (((y << 2) & 0xfc) | ((z >>> 8) & 0x03));		
		data[3]=(byte) (z);
	}
	
	/**
	 * Gets the path for the raw data file by day and hour.
	 *
	 * @return the path by time
	 */
	private String getFilePathByTime(Calendar time)
	{
		Date timeStamp = time.getTime();
		SimpleDateFormat day = new SimpleDateFormat("yyyy-MM-dd");
		SimpleDateFormat hour = new SimpleDateFormat("HH");

		String path = localPath +day.format(timeStamp)+"/"+hour.format(timeStamp)+"/";
		return path;
	}
	/**
	 * Checks the file name for current hour. If there is a file exists, return it; if not, generate the file name by the time. 
	 *
	 * @param path the path
	 * @return the file name for current hour
	 */
	private String getFileNameForCurrentHour(String path, Calendar time, final String ID){
		File dir = new File(path);
		String[] files = dir.list(new FilenameFilter() {
			
			@Override
			public boolean accept(File dir, String filename) {
				// TODO Auto-generated method stub
				return filename.contains("WocketSensor."+ID);
			}
		});
		if(files == null || files.length == 0)
			return generateFileNameByTime(time, ID);
		else
			return files[0];
	}

	/**
	 * Generate the raw file name by time. ID is assigned by default.
	 *
	 * @return the string
	 */
	private String generateFileNameByTime(Calendar time, String ID)
	{
		Date timeStamp = time.getTime();
		SimpleDateFormat detailedTime = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-SSS");
		String fileName="WocketSensor."+ID+"."+detailedTime.format(timeStamp)+".baf";		
		return fileName;
	}
	/**
	 * get sensor ID from MacID in configuration file
	 */
	/*private String getIDFromConfigurationFile(Calendar time, String MacID){
	    try {
		    SAXParserFactory spf = SAXParserFactory.newInstance(); 
		    SAXParser sp = spf.newSAXParser(); 
		    XMLReader xr = sp.getXMLReader(); 
		    SensorDataFileChecker dataHandler = new SensorDataFileChecker(); 
		    xr.setContentHandler(dataHandler); 
			Date now = time.getTime();
			SimpleDateFormat day = new SimpleDateFormat("yyyy-MM-dd");
			String path = localPath+ day.format(now) + "/wockets/";
			File sensorInfoFile = new File(path+configurationFileName);
			if(sensorInfoFile.exists()){
				xr.parse(new InputSource(new FileInputStream(sensorInfoFile)));
			}
			for (SensorDataInfo sensor : dataHandler.sensors) {
				if(sensor.getMacID().equals(MacID))
					return String.format("%02d",sensor.getID());
			}
			return null;		
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    return null;

	}
	/**
	 * save raw data as well for testing purpose
	 * @param time
	 * @param accelPoints
	 * @param ID
	 */
	/*private void outputRawDataInCSV(Calendar time, ArrayList<AccelPoint> accelPoints, String ID){
		long startTime = time.getTimeInMillis() - accelPoints.size()*FAKE_TIME_DIFF;
		String content = "";
		AccelPoint accelPoint = null;
		for (int i = 0; i < accelPoints.size(); i++) {
			accelPoint = accelPoints.get(i);
			content += (startTime+i*FAKE_TIME_DIFF)+","+accelPoint.getmX()+","+accelPoint.getmY()+","+accelPoint.getmZ()+"\r\n";
		}
		BufferedWriter writer = null;
		try {
			File file = new File(getFilePathByTime(time)+"record"+ID+".csv");
			if(!file.exists())
				file.createNewFile();
			writer = new BufferedWriter(new FileWriter(file,true));
			writer.write(content);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} finally{
			try{
				if(writer != null){
					writer.flush();
					writer.close();
				}
			}catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
			  	} 
		}
	}*/
}
