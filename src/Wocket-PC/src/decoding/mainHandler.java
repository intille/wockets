package decoding;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;

public class mainHandler 
{
	
	//private Calendar stamp;

	public Object enCode(Calendar stamp, int x, int y, int z)
	{
		//Calendar stamp=str2Cal(dateString);
		timeHandler t=new timeHandler();
		Filewriter fw=new Filewriter();
		ConvertData c= new ConvertData();
		fw.toFile(t.timeCalc(stamp),c.encoData( x, y, z));
		return null;
		
	}
	
	public static Calendar str2Cal(String dateString)
	{
		Calendar stamp = null;
		SimpleDateFormat _DateFormat_log = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");
		Date date;
		try {
			date = (Date)_DateFormat_log.parse(dateString);
			Calendar timeStamp=Calendar.getInstance();
			timeStamp.setTime(date);
			stamp=timeStamp;
		} catch (ParseException e) {
			e.printStackTrace();
		} 
		return stamp;
	}
	
	

}
