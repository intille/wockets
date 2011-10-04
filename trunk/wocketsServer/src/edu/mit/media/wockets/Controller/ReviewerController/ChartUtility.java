/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Controller.ReviewerController;

import net.sf.json.JSONArray;
import net.sf.json.JSONObject;

import java.util.Calendar;
import java.util.List;

public class ChartUtility {
	
/*****Returns the Data JSON object which has UTC time and data
 * e.g dataJSON = [[12222045555,10],[454454512,21],[14356565,null],.....]
 */
	public static JSONArray getChartSeriesJSON(List list,int dateIndx,int dataIndx)
	{
		int prevHr = 0;
		int prevMin = 0;
		StringBuilder sb = new StringBuilder();
		JSONArray dataJSON = new JSONArray();
		for(int n=0; n <list.size(); n++)
		{
			Object[] objectList = (Object[])list.get(n);
			String date = objectList[dateIndx].toString();//get date by dateIndx datetime format is "YYYY-MM-DD HH:mm:ss"
			int hr = Integer.parseInt(date.split(" ")[1].split(":")[0]);//get hour from datetime string
	            
	            if(n ==0)//check first value start with 0 hr or not
	            {
	                if(hr !=0)
	                {
	                    for(int x=0;x<60;x++)
	                    {
	                        sb.delete(0, sb.length());
	                        sb.append(convertToUTC(date.split(" ")[0]+" 0:"+x+":00"));//convert date to UTC time and add to String builder
	                        JSONArray data = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
	                        //data.add(Long.parseLong(sb.toString()));
	                        data.add(sb.toString());
	                        data.add(null);
	                        dataJSON.add(data);
	                    }
	                }
	            }
	            
	            if(hr != prevHr)//When data hour change
	            {
	                //check last inserted minute if its not 59 then insert null value for remaining minute
	                int nbrOfNullMin = 59 - prevMin;
	                if(nbrOfNullMin > 1 && nbrOfNullMin !=59)
	                {
	                    for(int m=1;m<=nbrOfNullMin ;m++)
	                    {
	                        sb.delete(0, sb.length());
	                        sb.append(convertToUTC(date.split(" ")[0]+" "+(prevHr)+":"+(prevMin+m)+":00"));
	                        JSONArray data = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
	                        //data.add(Long.parseLong(sb.toString()));
	                        data.add(sb.toString());
	                        data.add(null);
	                        dataJSON.add(data);

	       	             }
	                 }
	 
	                //check hour difference between last inserted value and currenthour if its > 1 then insert remaining null value
	                int hrDiff = (hr - prevHr);
	                if(hrDiff >1)
	                {
	                    for(int x=1;x<hrDiff;x++)
	                    {
	                        for(int y=0;y<60;y++)//insert null value for minutes 0 to 59
	                        {                               
	                            sb.delete(0, sb.length());
	                            sb.append(convertToUTC(date.split(" ")[0]+" "+(prevHr+x)+":"+y+":00"));
	                            JSONArray data = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
		                        //data.add(Long.parseLong(sb.toString()));
	                            data.add(sb.toString());
		                        data.add(null);
		                        dataJSON.add(data);
	                            prevMin = 0;
	                        }
	                    }
	                }
	            }
	            
	            int min = Integer.parseInt(date.split(" ")[1].split(":")[1]);//get minute
	            if(min != prevMin)//when minute change from prev value
	            {
	                int minDiff = (min - prevMin); //missing minutes between prev and current
	                if( minDiff > 1)
	                {
	                    int i = 1;
	                    if(prevMin==0)
	                        i = 0;

	                    for(;i<minDiff;i++)
	                    {
	                        sb.delete(0, sb.length());
	                        sb.append(convertToUTC(date.split(":")[0]+":"+(prevMin+i)+":00"));
	                        JSONArray data = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
	                        //data.add(Long.parseLong(sb.toString()));
	                        data.add(sb.toString());
	                        data.add(null);
	                        dataJSON.add(data);
	                    }
	                }
	            }
	            JSONArray data = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
                sb.delete(0, sb.length());
                sb.append(convertToUTC(date));
	            //data.add(Long.parseLong(sb.toString()));
                data.add(sb.toString());
                data.add(Float.parseFloat(objectList[dataIndx].toString()));//add value by dataIndx index from objectLIst
                dataJSON.add(data);//insert current data
  

	            if(n == list.size()-1)//if current data is last data
	            {
	                int nbrOfNullMin = 59 - prevMin;//check missing minutes for last data
	                if(nbrOfNullMin > 1)
	                {
	                    for(int m=1;m<=nbrOfNullMin ;m++)
	                    {
	                        sb.delete(0, sb.length());
	                        sb.append(convertToUTC(date.split(":")[0]+":"+(prevMin+m)+":00"));
	                        JSONArray d = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
	                        //d.add(Long.parseLong(sb.toString()));
	                        d.add(sb.toString());
	                        d.add(null);
	                        dataJSON.add(d);
	                    }

	                }
	                    
	                int diff = 23-hr;//check missing hours
	                if(diff >1)
	                {
	                    for(int x=1;x<=diff;x++)
	                    {
	                        for(int y=0;y<60;y++)//put null for each minute
	                        {                               
	                            sb.delete(0, sb.length());
	                            sb.append(convertToUTC(date.split(" ")[0]+" "+(prevHr+x)+":"+y+":00"));
		                        JSONArray d = new JSONArray();//create a data JSON object which has time and value e.g.[2011-08-12 11:02:30, null]
		                        //d.add(Long.parseLong(sb.toString()));
		                        d.add(sb.toString());
		                        d.add(null);
		                        dataJSON.add(d);
	                        }
	                    }
	                }
	             }
	                prevHr = hr;
	                prevMin = min;

	           } // main for loop close
		return dataJSON;
	}
	
	//return UTC time string
	public static String convertToUTC(String timeStr)
    {
        String date = timeStr.split(" ")[0];//date string
        String time = timeStr.split(" ")[1];//time string
        
        int year = Integer.parseInt(date.split("-")[0]);
        int month = Integer.parseInt(date.split("-")[1]);
        int day = Integer.parseInt(date.split("-")[2]);
        
        int hr = Integer.parseInt(time.split(":")[0]);
        int min = Integer.parseInt(time.split(":")[1]);
        int sec = (int)Float.parseFloat((time.split(":")[2]));
        String utcTime = "Date.UTC("+year+","+(month-1)+","+day+","+hr+","+min+","+sec+")";
        return utcTime;
        
   }
	
}
