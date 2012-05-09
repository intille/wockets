package DataCollection;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;


//import android.content.SharedPreferences;
//import android.util.Log;
//import java.util.logging.*;

public class Logger 
{
	public static String logPath;
	public static BufferedWriter bw;
	public static FileWriter fstream;
	public static final String PREF_FILE_NAME = "WocketsPrefFile";
	private static SimpleDateFormat _DateFormat_log = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");
	static Boolean flag= false; 
	//private static PrintWriter out = null;
	
	private Logger()
	{
		
	}
	
	public static void log(int sensorid,String msg)
	{		
		//DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
		//Calendar cal = Calendar.getInstance();
		//String dataStoragePath = dateFormat.format(cal.getTime()).toString();
		Calendar logDt = Calendar.getInstance();
    	logDt.setTimeInMillis(System.currentTimeMillis());
        Date logTmpDt = logDt.getTime();
		
		//logPath = "C:/log"+dataStoragePath;
		/*logPath = "C:\\log";
		File logFile = new File(logPath);
		try
		{
			logFile.mkdirs();
		}
		catch(SecurityException ex)
		{
			//Log.e("LOG","Unable to create log directory");
			System.out.println("Unable to create log directory");
		}
		
		logFile = null;
		
		logFile = new File(logPath + "log" + sensorid + ".csv");
		
		
        
        if(!logPath.equals(""))
        {
        	try 
    		{
    			//bw = new BufferedWriter(new FileWriter(logFile,true));
    			//bw.write(_DateFormat_log.format(logTmpDt) + "," + msg);
    			//bw.write("\n");
    			//bw.flush();
    			//bw.close();
        		fstream = new FileWriter("out.csv");        		
      		  	out = new BufferedWriter(fstream);
      		  	out.append(_DateFormat_log.format(logTmpDt) + "," + msg + "\n");
      		  	/*out.write(_DateFormat_log.format(logTmpDt) + "," + msg);
      		  	out.write("\n");
      		  	out.flush();
      		  	//Close the output stream
      		  	out.close();
    		} 
    		catch (IOException e) 
    		{
    			//Log.e("Logger", "Error while writing logs");
    			System.out.println("Error while writing logs");
    		}
        }
        
        */
        
        File f = new File("out.csv");
        PrintWriter out = null;
        try {
                if (!(f.exists())) {
                        f.createNewFile();
                }
                if (!flag){
                	out = new PrintWriter(new FileWriter("out.csv"));
                	flag = true;
                } else
                	out = new PrintWriter(new FileWriter("out.csv",true));
        }
        catch (IOException e1) {
                e1.printStackTrace();
        }
        
        String s = _DateFormat_log.format(logTmpDt) + "," + msg + "\n";
        try {
                //out.println(s);
        	out.append(s);
        }
        catch (NumberFormatException e) {
        	System.out.println("Error while writing logs");
        }
        
        if (out != null) {
                out.close();
        }
		
	}
	
	public static void debug(String msg)
	{
		//SharedPreferences pref = WocketsService._Context.getSharedPreferences(PREF_FILE_NAME, WocketsService.MODE_PRIVATE);
		//String dataStoragePath = pref.getString("DATASTORAGEPATH", "");
		DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
		Calendar cal = Calendar.getInstance();
		String dataStoragePath = dateFormat.format(cal.getTime()).toString();
		logPath = dataStoragePath;
		File logFile = new File(logPath);
		try
		{
			logFile.mkdirs();
		}
		catch(SecurityException ex)
		{
			//Log.e("LOG","Unable to create log directory");
			System.out.println("Unable to create log directory");
		}
		
		logFile = null;

		logFile = null;
		logFile = new File(logPath + "debug.csv");
		
		Calendar logDt = Calendar.getInstance();
    	logDt.setTimeInMillis(System.currentTimeMillis());
        Date logTmpDt = logDt.getTime();
        
        if(!logPath.equals(""))
        {
        	try 
    		{		
    			bw = new BufferedWriter(new FileWriter(logFile,true));
    			bw.write(_DateFormat_log.format(logTmpDt) + "," + msg);
    			bw.write("\n");
    			bw.flush();
    			bw.close();
    		}
    		catch (IOException e) 
    		{
    			//Log.e("Logger", "Error while writing to debug.csv");
    			System.out.println("Error while writing to debug.csv");
    		}
        }
	}
	
	public static void error(String msg)
	{
		//SharedPreferences pref = WocketsService._Context.getSharedPreferences(PREF_FILE_NAME, WocketsService.MODE_PRIVATE);
		//String dataStoragePath = pref.getString("DATASTORAGEPATH", "");
		DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
		Calendar cal = Calendar.getInstance();
		String dataStoragePath = dateFormat.format(cal.getTime()).toString();
		logPath = dataStoragePath;
		File logFile = new File(logPath);
		try
		{
			logFile.mkdirs();
		}
		catch(SecurityException ex)
		{
			//Log.e("LOG","Unable to create log directory");
			System.out.println("Unable to create log directory");
		}
		
		logFile = null;
		
		logFile = new File(logPath + "error.csv");
		
		Calendar logDt = Calendar.getInstance();
    	logDt.setTimeInMillis(System.currentTimeMillis());
        Date logTmpDt = logDt.getTime();
        if(!logPath.equals(""))
        {
        	try 
    		{		
    			bw = new BufferedWriter(new FileWriter(logFile,true));
    			bw.write(_DateFormat_log.format(logTmpDt) + "," + msg);
    			bw.write("\n");
    			bw.flush();
    			bw.close();
    		}
    		catch (IOException e) 
    		{
    			//Log.e("Logger", "Error while writing to error.csv");
    			System.out.println("Error while writing to debug.csv");
    		}
        }
		
	}
	
	public void Dispose()
	{
		try
		{
			bw.flush();
		}
		catch(IOException e)
		{
			//Log.e("Logger","Error while disposing logger");
			System.out.println("Error while disposing logger");
		}
	}
}
