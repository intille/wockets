package bafFormat;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.OutputStream;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;


public class BafDecoder{
	private final static String TAG = "DataDecoder";
	private static String localPath;
	private static String configurationFileName = "SensorData.xml";

	private static long timeStamp;
	private static int[] dataValues;
	private final static int fullTimeLength = 8;
	private final static int diffTimeLength = 1;
	private final static int uncompressedDataLength = 4;
	private final static int compressedDataLength = 2;
	private byte[] temp_FullTime;
	private byte temp_DiffTIme;
	private byte[] temp_CompressedData;
	private byte[] temp_UnCompressedData;
	
	public BafDecoder() {
		super();
/*********************File Path in Android*******************************************************/
//		this.localPath = Environment.getExternalStorageDirectory().getAbsolutePath() + "/.wockets/data/";
/*********************File Path in PC************************************************************/
		this.localPath = "c:/test/";
/************************************************************************************************/
		resetPrevData();
	}	
	
	private void resetPrevData(){
		dataValues = new int[3];
		timeStamp = 0;
		temp_FullTime = new byte[fullTimeLength];
		temp_CompressedData = new byte[compressedDataLength];
		temp_UnCompressedData = new byte[uncompressedDataLength];
	}
	
	/**
	 * Decode and save data with stream.
	 *
	 * @param startTimeInDate the startTimeInDate must be in YYYY-MM-DD hh:mm format
	 * @param endTimeInDate the endTimeInDate must be in YYYY-MM-DD hh:mm format
	 * @param MacID the mac id
	 */
	public void decodeAndSaveDataWithStream(Date startTimeInDate, Date endTimeInDate, String MacID){
		if(startTimeInDate.getDate() != endTimeInDate.getDate()){
			System.out.println("Error in DataDecoder: start time and end time are not in the same day.");
			return;
		}
		SimpleDateFormat dayFormat = new SimpleDateFormat("yyyy-MM-dd");
/*********************Get sensor ID from configuration file in Android*****************************/
		//SensorDataInfo sensor = getSensorInfoFromConfigurationFile(dayFormat.format(startTimeInDate), MacID);
		//String ID = String.format("%02d",sensor.getID());
		//String outputFileName = getRawDataFileName(sensor,ID);
/*********************Set temporary dummy ID in PC ************************************************/
		String ID = MacID;
		String outputFileName = "Wocket_"+ ID +"_RawData_Dominant-Ankle.csv";
/**************************************************************************************************/
		String outputFilePath = getAbsoluteOutputPath(dayFormat.format(startTimeInDate));
		clearOldDecodedFiles(dayFormat.format(startTimeInDate), ID);
		BufferedInputStream inputStream = null;
		BufferedOutputStream outputStream = null;
		try{
			long startTimeInMillis = startTimeInDate.getTime();
			long endTimeInMillis = endTimeInDate.getTime();

			String[] inputFileNames = sortFileNameByHour(getRawDataFileNamesByTime(dayFormat.format(startTimeInDate),
					startTimeInDate.getHours(), endTimeInDate.getHours(), ID));
			if(inputFileNames.length == 0){
				System.out.println("Error: no files found between start time and end time");
				return;
			}
			
			//output file
			File outputDir = new File(outputFilePath);
			if(!outputDir.isDirectory())
				outputDir.mkdirs();
			File outputFile = new File(outputFilePath+outputFileName);
			if(!outputFile.exists())
				outputFile.createNewFile();
			outputStream = new BufferedOutputStream(new FileOutputStream(outputFile,true));

			outputStream = (BufferedOutputStream) decodeBytesWithinHour(inputFileNames[0], startTimeInMillis, endTimeInMillis, outputStream);
			if(inputFileNames.length > 1){
				for (int i = 1; i < inputFileNames.length-1; i++) {
					outputStream = (BufferedOutputStream) decodeBytesForWholeFile(inputFileNames[i], outputStream);
				}
				outputStream = (BufferedOutputStream) decodeBytesWithinHour(inputFileNames[inputFileNames.length-1], startTimeInMillis, endTimeInMillis, outputStream);
			}
			System.out.println("Finish decoding baf file.");
		} catch (IOException e){
			System.out.println("Error in file I/O :"+e.toString());
		} finally{
			try {
				if(inputStream != null)
					inputStream.close();
				if(outputStream != null){
					outputStream.flush();
					outputStream.close();
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				System.out.println("Can not close file stream."+ e.toString());
			}
		}
	}

		
	private void decodeUnCompressedData(byte[] data)
	{
		if(data !=null && data.length == uncompressedDataLength){
			dataValues = new int[3];
			dataValues[0] = (int)(data[0] & 0x3f);
			dataValues[0] = (((dataValues[0] << 4) & 0x03f0) | ((data[1] >>> 4) & 0x0f)) & 0x3ff;
			dataValues[1] = (int)(data[1] & 0x0f);
			dataValues[1] = (((dataValues[1] << 6) & 0x03c0) | ((data[2] >>> 2) & 0x3f)) & 0x3ff;
			dataValues[2] = (int)(data[2] & 0x03);
			dataValues[2] = (((dataValues[2] << 8) & 0x0300) | (data[3] & 0x00ff)) & 0x3ff;
		}
		else{
			System.out.println("Error in decoding uncompressed data.");
			return;
		}
	}
	 
	private void decodeCompressedData(byte[] data)
	{
		if(data !=null && data.length == compressedDataLength){
			int[] diffValues = new int[3];
			diffValues[0] = (int) (data[0] >> 2) & 0x1f;
			diffValues[1] = (int) ((data[0] << 3) & 0x18) | ((data[1] >> 5) & 0x07);
			diffValues[2] = (int) data[1] & 0x1f;
			for (int i = 0; i < diffValues.length; i++) {
				if((diffValues[i] & 0x10) != 0)
					diffValues[i] = (diffValues[i] & 0x0f) * (-1);
			}
			for (int i = 0; i < dataValues.length; i++) {
				dataValues[i] += diffValues[i];
			}
		}
		else{
			System.out.println("Error in decoding compressed data.");
			return;
		}

	}
	private void  decodeFullTimeStamp(byte[] fullTimeStamp){
		if(fullTimeStamp != null && fullTimeStamp.length == fullTimeLength){
			int year = 0, month = 0, day = 0;
			int millis = 0;
			year = (int)(fullTimeStamp[0] & 0x7f);
			year = (int) (((year << 8) & 0x7f00)|(fullTimeStamp[1]&0x00ff));
			month = fullTimeStamp[2] - 1;
			day = fullTimeStamp[3];
			millis = (int)fullTimeStamp[4]&0x00ff;
			millis = (((millis << 8) & 0xff00)|((int)fullTimeStamp[5]&0x00ff));
			millis = ((millis << 8) & 0xffff00)|((int)fullTimeStamp[6]&0x00ff);
			millis = ((millis << 8) & 0xffffff00)|((int)fullTimeStamp[7]&0x00ff);
			int hour = millis/(60*60*1000);
			int min = (millis - hour*60*60*1000)/(60*1000);
			int sec = (millis - hour*60*60*1000 - min*60*1000)/1000;
			Calendar time = Calendar.getInstance();
			time.set(year, month, day, hour, min, sec);
			time.set(Calendar.MILLISECOND, millis%1000);
			timeStamp = time.getTimeInMillis();
		}
		else{
			System.out.println("Error in full time stamp decodig.");
			return;
		}
	}
	private void decodeDiffTimeStamp(byte diffTimeStamp){
		timeStamp += diffTimeStamp;
	}
	
	/**
	 * Gets the raw data file names by time.
	 *
	 * @param dataStamp the data stamp must be in YYYY-MM-DD format
	 * @param startHour the start hour
	 * @param endHour the end hour
	 * @param ID the iD
	 * @return the raw data file names by time
	 */
	private String[] getRawDataFileNamesByTime(String dataStamp, int startHour, int endHour,final String ID){
		if(!dataStamp.matches("\\d{4}-\\d{2}-\\d{2}")){
			System.out.println("Error: date is not in the right format");
			return null;
		}
		ArrayList<String> fileList = new ArrayList<String>();
		File dataFolder = new File(localPath);
		String[] days = dataFolder.list();	
		if(days == null || days.length == 0)
			return null;
		for (String day : days) {
			if(day.equals(dataStamp)){
				File dayFolder = new File(localPath+day);
				if(dayFolder.isDirectory()){
					String[] hours = dayFolder.list(new FilenameFilter() {
						
						@Override
						public boolean accept(File dir, String filename) {							
							return filename.matches("\\d{2}");
						}
					});
					int[] hoursNum = new int[hours.length];
					for (int i = 0; i < hours.length; i++) {
						hoursNum[i] = Integer.parseInt(hours[i]);
					}
					for (int hourNum : hoursNum) {
						if(hourNum >= startHour && hourNum <= endHour){
							String hour = String.format("%02d", hourNum);
							File hourFolder = new File(localPath+day+"/"+hour);
							if(hourFolder.isDirectory()){
								String[] files = hourFolder.list(new FilenameFilter() {
									
									@Override
									public boolean accept(File dir, String filename) {
										// TODO Auto-generated method stub
										return filename.contains("WocketSensor."+ID);
									}
								});
								for (String fileName : files) {
									fileList.add(localPath+day+"/"+hour+"/"+fileName);
								}
							}
						}
					}
				}

			}
		}
		String[] fileNames = new String[fileList.size()];
		for (int i = 0; i < fileNames.length; i++) {
			fileNames[i] = fileList.get(i);
		}
		return fileNames;
	}
	
	private String[] sortFileNameByHour(String[] fileNames){
		try {
			String[] sortedFileNames = new String[fileNames.length];
			int[] hours = new int[fileNames.length];			
			String path = localPath;
			int sum = 0;
			for (int i = 0; i < fileNames.length; i++) {
				hours[i] =Integer.parseInt(fileNames[i].substring(path.length()+11, 
						path.length()+13));
				sum+=hours[i];
			}
			for (int i = 0; i < sortedFileNames.length; i++) 
				for (int j = 0; j < hours.length; j++) 
					if(hours[j] ==((int)(sum/fileNames.length)+(int)(fileNames.length/2) - fileNames.length + i+1)){
						sortedFileNames[i] = fileNames[j];
			}
			return sortedFileNames;
		
		} catch(NumberFormatException e){
			System.out.println("Can not sort time by time, file name error -- "+e.toString());
		} 
		return null;
	}

	private String getAbsoluteOutputPath(String date){
  	    String path =  localPath+date+"/merged/";
  	    return path;
	}
/***************The following part of code is only for using configuration file to get ID and body location************/
	/*private SensorDataInfo getSensorInfoFromConfigurationFile(String now, String MacID){
		if(!now.matches("\\d{4}-\\d{2}-\\d{2}")){
			Log.e(TAG, "Error: date is not in the right format");
			return null;
		}
	    try {
		    SAXParserFactory spf = SAXParserFactory.newInstance(); 
		    SAXParser sp = spf.newSAXParser(); 
		    XMLReader xr = sp.getXMLReader(); 
		    SensorDataFileChecker dataHandler = new SensorDataFileChecker(); 
		    xr.setContentHandler(dataHandler); 
			String path = localPath+ now + "/wockets/";
			File sensorInfoFile = new File(path+configurationFileName);
			if(sensorInfoFile.exists()){
				xr.parse(new InputSource(new FileInputStream(sensorInfoFile)));
			}
			for (SensorDataInfo sensor : dataHandler.sensors) {
				if(sensor.getMacID().equals(MacID))
					return sensor;
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
	private String getRawDataFileName(SensorDataInfo sensor, String ID){
		String fileName = "Wocket_"+ID+"_RawData_";
		String[] locations = sensor.getBodyLocation().split(" ");
		if(sensor.isDominant())
			fileName += "Dominant-"+locations[locations.length - 1]+".csv";
		else
			fileName += Globals.nonDominantSide+"-"+locations[locations.length - 1]+".csv";
		return fileName;
	}*/
/*************************************************************************************************************************/
	private void clearOldDecodedFiles(String time, final String ID){
		if(!time.matches("\\d{4}-\\d{2}-\\d{2}")){
			System.out.println("Error: date is not in the right format");
			return;
		}
		File dict = new File(getAbsoluteOutputPath(time));
		if(dict.exists()){
			if(dict.isDirectory()){
				File[] files = dict.listFiles(new FilenameFilter() {
					
					@Override
					public boolean accept(File dir, String filename) {
						// TODO Auto-generated method stub
						return filename.contains("WocketSensor_"+ID);
					}
				});
				for (File file : files) {
					file.delete();
				}
			}
		}
	}
	
	private OutputStream decodeBytesWithinHour(String inputFileName, long startTimeInMillis, long endTimeInMillis, OutputStream outputStream){
		BufferedInputStream inputStream = null;
		try {
			File inputFile = new File(inputFileName);
			if(!inputFile.exists()){
				System.out.println("Input file doesn't exist.");
				return outputStream;
			}
			inputStream = new BufferedInputStream(new FileInputStream(inputFile));
			int readData;
			readData = inputStream.read();
			while(readData != -1){
				if((readData & 0x80) == 0){ //case: differential time stamp
					temp_DiffTIme = (byte)readData;
					decodeDiffTimeStamp(temp_DiffTIme);
					if(timeStamp >= startTimeInMillis && timeStamp <= endTimeInMillis)
						outputStream.write((timeStamp+"").getBytes());
					else if(timeStamp > endTimeInMillis){
						readData = -1;
						break;
					}
				}else{//case: full time stamp
					temp_FullTime[0] = (byte)readData;
					inputStream.read(temp_FullTime, 1, temp_FullTime.length-1);
					decodeFullTimeStamp(temp_FullTime);
					if(timeStamp >= startTimeInMillis && timeStamp <= endTimeInMillis)
						outputStream.write((timeStamp+"").getBytes());
					else if(timeStamp > endTimeInMillis){
						readData = -1;
						break;
					}
				}
				
				readData = inputStream.read();
				if((readData & 0x80) == 0){ //case: compressed data
					temp_CompressedData[0] = (byte)readData;
					inputStream.read(temp_CompressedData, 1, temp_CompressedData.length-1);
					decodeCompressedData(temp_CompressedData);
					if(timeStamp >= startTimeInMillis && timeStamp <= endTimeInMillis){
						for (int data : dataValues) {
							outputStream.write((","+data).getBytes());
						}
					}
				}else{//case: uncompressed data
					temp_UnCompressedData[0] = (byte)readData;
					inputStream.read(temp_UnCompressedData, 1, temp_UnCompressedData.length-1);
					decodeUnCompressedData(temp_UnCompressedData);
					if(timeStamp >= startTimeInMillis && timeStamp <= endTimeInMillis){
						for (int data : dataValues) {
							outputStream.write((","+data).getBytes());
						}	
					}
				}
				if(timeStamp >= startTimeInMillis && timeStamp <= endTimeInMillis)
					outputStream.write(("\r\n").getBytes());
				readData = inputStream.read();
			}
//			outputStream.flush();
			return outputStream;
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} finally{
				try {
					if(inputStream != null)
						inputStream.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
		}
		return outputStream;
	}
	
	private OutputStream decodeBytesForWholeFile(String fileName, OutputStream outputStream){
		BufferedInputStream inputStream = null;
		try {
			File inputFile = new File(fileName);
			if(!inputFile.exists()){
				System.out.println("Input file doesn't exist.");
				return outputStream;
			}
			
			inputStream = new BufferedInputStream(new FileInputStream(inputFile));
			int readData;
			
			readData = inputStream.read();
			while(readData != -1){
				if((readData & 0x80) == 0){ //case: differential time stamp
					temp_DiffTIme = (byte)readData;
					decodeDiffTimeStamp(temp_DiffTIme);
					outputStream.write((timeStamp+"").getBytes());
				}else{//case: full time stamp
					temp_FullTime[0] = (byte)readData;
					inputStream.read(temp_FullTime, 1, temp_FullTime.length-1);
					decodeFullTimeStamp(temp_FullTime);
					outputStream.write((timeStamp+"").getBytes());
				}
				
				readData = inputStream.read();
				if((readData & 0x80) == 0){ //case: compressed data
					temp_CompressedData[0] = (byte)readData;
					inputStream.read(temp_CompressedData, 1, temp_CompressedData.length-1);
					decodeCompressedData(temp_CompressedData);
					for (int data : dataValues) {
						outputStream.write((","+data).getBytes());
					}
				}else{//case: uncompressed data
					temp_UnCompressedData[0] = (byte)readData;
					inputStream.read(temp_UnCompressedData, 1, temp_UnCompressedData.length-1);
					decodeUnCompressedData(temp_UnCompressedData);
					for (int data : dataValues) {
						outputStream.write((","+data).getBytes());
					}
				}
				outputStream.write(("\r\n").getBytes());
	
				readData = inputStream.read();
			}
//			outputStream.flush();
			return outputStream;
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} finally{
			try {
				if(inputStream != null)
					inputStream.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
	}
		return outputStream;
	}
}
