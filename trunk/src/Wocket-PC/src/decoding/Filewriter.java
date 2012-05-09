package decoding;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;

public class Filewriter 
{
	private static String prevFileName=null, prevParentName=null;
	private Calendar fullStamp;
	private static int prevHR=0;
	public String instOf(Object time)
	{
		Calendar timer=(Calendar) time;
		String timeStamp;
		timeStamp=instOf(timer);
		return timeStamp;
	}
	
	public String instOf(Calendar time)
	{		
		String timeStamp;	
		SimpleDateFormat sdf = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");
		time.setTimeInMillis(time.getTimeInMillis());
		Date logTmpDt=time.getTime();
		timeStamp=sdf.format(logTmpDt);		
		return timeStamp;

	}
	public void toFile(Object time, byte [] finalData)
	{
		String timeStamp;
		String finDat;
		fullStamp=Calendar.getInstance();
		//Check to see whether time stamp is  a complete or an offset from the
			//previous one
		if (time instanceof Integer)
		{
			int timer=(int) fullStamp.getTimeInMillis();
			timer=timer+Integer.parseInt((time.toString()));
			fullStamp.setTimeInMillis(timer);
			
			timeStamp =time.toString();
		}
		else
		{
			
			fullStamp=(Calendar) time;
			timeStamp=instOf(time);
			
			
		}
			
		//Generates the string to write to the file
		finDat=timeStamp+","+finalData[0]+","+finalData[1];
		if(finalData.length>2)
		{
			finDat=timeStamp+","+finalData[0]+","+finalData[1]+","+finalData[2]+","+finalData[3];
		}
		
		this.addToFile(time, finDat);
	}
	
	
	public void addToFile (Object time, String s) 
	{

	      BufferedWriter bw = null;
	      try 
	      {
	    	 FileChecker fc=new FileChecker(); 
	    	 String  fileName;
	    	 String parent;	    	
//	    	 String parent=parentNameGenerator((Calendar) time);
//	    	 parent=fc.fileCheck(parent);
	    	 int HR=0;
	    	 if(!(time instanceof Integer))
    		 {
	    		 Calendar stamp;
		    	 stamp=(Calendar) time;
		    	 HR=stamp.get(Calendar.HOUR_OF_DAY); 
    		 }
	    	 
	    
	    	 if(time instanceof Integer || HR==prevHR)
	    		 {
//	    		 	if(HR==prevHR && !(time instanceof Integer))
//	    		 		System.out.println("HR="+HR+" prevHR="+prevHR);
	    		 	//System.out.println(".");
	    		 	if(prevParentName==null)
	    		 		parent=parentNameGenerator((Calendar) time);
	    		 	else
	    		 		parent=prevParentName;
	    		 	
	    		 	if(prevFileName==null)
	    		 	{
	    		 		String check=fc.fileCheck(parent);
		    		 	if(check==null)
		    		 		fileName=fileNameGenerator((Calendar) time);
		    		 	else
		    		 		fileName=check;
	    		 	}
	    		 	else
	    		 		fileName=prevFileName;
	    		 	
	    		 }
	    	 else
	    		 {
	    		 	parent=parentNameGenerator((Calendar) time);
	    		 	String check=fc.fileCheck(parent);
	    		 	//System.out.println(".2");
	    		 	if(check==null)
	    		 		fileName=fileNameGenerator((Calendar) time);
	    		 	else
	    		 		fileName=check;
	    		 	prevHR=HR;
	    		 }
	    	 //System.out.println(parent+fileName);	    	 
	    	 File file=new File(parent, fileName);
	    	 if (!file.isFile())
	    		 	(new File(parent)).mkdirs();
	    		 
	         bw = new BufferedWriter(new FileWriter(file, true));
	         bw.write(s);
	         bw.newLine();
	         bw.flush();
	      } 
	      catch (IOException ioe) 
	      {
	    	  ioe.printStackTrace();
	      } 
	      finally 
	      {                       //close the file
	    	  if (bw != null) try 
	    	  {
	    		 
	    		 bw.close();
	    	  } 
	    	  catch (IOException ioe2) 
	    	  {
	    		  // Not doing anything
	    	  }
	      } // end try/catch/finally

	   } // end test()
	
	
	//Dynamically generates a directory tree to store the data in
	public String parentNameGenerator(Calendar stamp)
	{

		int month=stamp.get(Calendar.MONTH)+1;
		int day=stamp.get(Calendar.DAY_OF_MONTH );
		int hour=stamp.get(Calendar.HOUR_OF_DAY);
		String MO;
		String DY;
		String HR;
		if(month<10)
			MO=String.valueOf("0"+month);
		else
			MO=String.valueOf(month);
		if(day<10)
			DY=String.valueOf("0"+day);
		else
			DY=String.valueOf(day);
		if(hour<10)
			HR=String.valueOf("0"+hour);
		else
			HR=String.valueOf(hour);
		
		String YEAR=String.valueOf(stamp.get(Calendar.YEAR));
		
		String location="c:/test/";
		
//		String HR=String.valueOf(stamp.get(Calendar.HOUR_OF_DAY));			
		String parentName = null;				
		parentName=location+YEAR+"-"+MO+"-"+DY+"/"+HR+"/";
		//System.out.println(parentName);
		prevParentName=parentName;
		return parentName;
	}
	
	
	// Dynamically generates file name to store the data in
	public String fileNameGenerator(Calendar stamp)
	{
		String SensorType="WocketSensor";
		String ID="007";
		int month=stamp.get(Calendar.MONTH)+1;
		int day=stamp.get(Calendar.DAY_OF_MONTH );
		int hour=stamp.get(Calendar.HOUR_OF_DAY);
		String YEAR=String.valueOf(stamp.get(Calendar.YEAR));
		String MO;
		String DY;
		String HR;
		if(month<10)
			MO=String.valueOf("0"+month);
		else
			MO=String.valueOf(month);
		if(day<10)
			DY=String.valueOf("0"+day);
		else
			DY=String.valueOf(day);
		if(hour<10)
			HR=String.valueOf("0"+hour);
		else
			HR=String.valueOf(hour);
		String MN=String.valueOf(stamp.get(Calendar.MINUTE));
		String MSe=String.valueOf(stamp.get(Calendar.MILLISECOND));				
		String fileName = null;				
		fileName=SensorType+"."+ID+"."+YEAR+"."+MO+"."+DY+"."+HR+"."+MN+"."+MSe+".baf";		
		prevFileName=fileName;
		return fileName;
	}
	
	

	

}
