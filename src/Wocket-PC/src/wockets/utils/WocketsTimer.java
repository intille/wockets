package wockets.utils;

import java.nio.ByteBuffer;
import java.util.Calendar;

public class WocketsTimer 
{
	//private static byte[] temp2 = new byte[2];
    private static byte[] temp4 = new byte[4];
    
	public static double UnixTimeFromBytes(byte[] someBytes)
	{
		int sec = DecodeUnixTimeSecBytes(someBytes);
		int ms = (int)DecodeUnixTimeMSBytesLong(someBytes);
		
		double ds = (double)sec;
		double dms = (double)ms;
		
		return((ds * 1000) + dms);
	}
	
	public static int DecodeUnixTimeSecBytes(byte[] someBytes)
	{		
		temp4[0] = someBytes[0];
        temp4[1] = someBytes[1];
        temp4[2] = someBytes[2];
        temp4[3] = someBytes[3];
        ByteBuffer bb = ByteBuffer.wrap(temp4);
        return bb.getInt(0);
	}
	
	public static long DecodeUnixTimeMSBytesLong(byte[] someBytes)
    {
        temp4[0] = someBytes[4];
        temp4[1] = someBytes[5];
        temp4[2] = 0;
        temp4[3] = 0;
        ByteBuffer bb = ByteBuffer.wrap(temp4);
        return bb.getInt(0);
    }
	
	public static Calendar DateTimeFromUnixTime(double unixTimeStamp)
	{
		Calendar origin = Calendar.getInstance();
		origin.set(1970, 1, 1, 0, 0, 0);
		long originms = origin.getTimeInMillis();
		originms += unixTimeStamp;
		
		Calendar now = Calendar.getInstance();
		now.setTimeInMillis(originms);
		
		return now;
	}
}
