/*Created By Salim Khan
 * Has all method to get chart data for selected participant and date
 */
package edu.mit.media.wockets.Controller.ReviewerController;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.hibernate.SQLQuery;
import org.hibernate.Session;

import edu.mit.media.wockets.utility.HibernateSession;
import net.sf.json.JSONArray;
import net.sf.json.JSONObject;

public class ReviewerControllerUtil {
	
	//return JSON object of user asigned Study list
	@SuppressWarnings("all")
	public static JSONObject getUserAssignedStudy(int userId)
	{
		Session session = HibernateSession.getSession();
		SQLQuery q = session.createSQLQuery("SELECT STUDY_TYPE.* FROM STUDY_TYPE INNER JOIN USER_ASSIGNED_STUDY "+
											"ON STUDY_TYPE.Study_Id = USER_ASSIGNED_STUDY.Study_Id " +
											"WHERE USER_ASSIGNED_STUDY.User_Id =:uId");
		q.setInteger("uId",userId);
		List list = q.list();
		HibernateSession.sessionClose(session);
		//create JSON object for dhtmlx
		JSONObject jObj =new JSONObject();//main JSON object
		JSONArray rowListObj=new JSONArray();//row JSON object

		for(int i=0 ;i<list.size();i++)
		{	
			Object[] objectList = (Object[])list.get(i);
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);						//each rows has unique Id
			JSONArray rowData=new JSONArray();		//Array JSON object has data for row
			rowData.add(objectList[0].toString());
			rowData.add(objectList[1].toString());
			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
		}
		jObj.put("rows",rowListObj);
		return jObj;
	}
	
	//reutrn JSON object of study participant list
	@SuppressWarnings("all")
	public static JSONObject getStudyParticipantList(String studyId)
	{
		Session session = HibernateSession.getSession();
		SQLQuery q = session.createSQLQuery("SELECT PARTICIPANT.Participant_Id,PARTICIPANT.First_Name,PARTICIPANT.Last_Name " +
											"FROM PARTICIPANT INNER JOIN PARTICIPANT_STUDY "+
											"ON PARTICIPANT.Participant_Id = PARTICIPANT_STUDY.Participant_Id "+
											"WHERE PARTICIPANT_STUDY.Study_Id =:sId");
		q.setString("sId",studyId);
		List list = q.list();
		HibernateSession.sessionClose(session);
		//create JSON object for dhtmlx
		JSONObject jObj =new JSONObject();//main JSON object
		JSONArray rowListObj=new JSONArray();//row JSON object

		for(int i=0 ;i<list.size();i++)
		{	
			Object[] objectList = (Object[])list.get(i);
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);						//each rows has unique Id
			JSONArray rowData=new JSONArray();		//Array JSON object has data for row
			rowData.add(objectList[0].toString());
			rowData.add(objectList[1].toString());
			rowData.add(objectList[2].toString());
			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
		}
		jObj.put("rows",rowListObj);
		return jObj;
	}
	
	
	public static JSONObject getchartData(int participantId,String date)
	{
		JSONObject chartJSONObj = new JSONObject();

		String[] dateArray = date.split("-");//split date "YYYY-MM-DD" based on "-"
		
		Session session = HibernateSession.getSession();
		//add wockets data and swapped flags
		JSONArray wktJsonList = getWocketsStatsData(participantId, dateArray, session);
		chartJSONObj.put("wocketData", wktJsonList);
		
		//add wockets swapped flags data
		JSONArray swappedFlags = getSwappedFlag(participantId, dateArray, session);
		chartJSONObj.put("swappedFlag", swappedFlags);

		//add phone stats data
		JSONArray phoneStats = getPhoneStats(participantId, dateArray, session);
		chartJSONObj.put("phoneStats", phoneStats);
		
		//add Raw-data-stats
		JSONObject rawDataStats = getRawDataStats(participantId, dateArray, session);
		chartJSONObj.put("rawDataStats", rawDataStats);
		
		//add sms JSON object
		JSONObject smsList = getSMSMssgs(participantId, dateArray, session);
		chartJSONObj.put("smsList", smsList);
		
		//add prompt JSON object
		JSONObject promptDetail = getPromptDetail(participantId, dateArray, session);
		chartJSONObj.put("promptList", promptDetail);
		
		//add hidden series to make Y-axis fix
		JSONObject hiddenSeries = getHiddenSeries(dateArray);
		chartJSONObj.put("hiddenSeries", hiddenSeries);
		
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
		return chartJSONObj;
	}
	
/**return the WocketJSON JSON Array
* Structure is---> wktsJsonList
* 						|
* 						|
* 						V
* 			Arrayof each wocket record --> Activity JSON object --> name:"activity series name"
* 										|							data:data:[[10000,1.5],[123455,1.5],[12365444,null],..]//1st value is UTC time and 2nd is activity value 
* 										|																				   //for each minute if not found then null
* 										|						
* 						                 -->Battery JSON Object--> name:"battery series name"
* 																	data:[]
* 
* 
*/

	//return mac Ids for participant for selected date
	public static ArrayList<String> getParticipnatMacIds(int participantId,String[] dateArray,Session session)
	{
		ArrayList<String> macIds = new ArrayList<String>();
		//get disticnt mac_id for selected day
		SQLQuery q = session.createSQLQuery("SELECT DISTINCT Mac_Id FROM Wockets_Stats "+
                                             "WHERE Participant_Id =:pId "+
                                             "AND YEAR(Create_Date) =:year "+
                                             "AND MONTH(Create_Date) =:month "+
                                             "AND DAY(Create_Date) =:day");
		q.setInteger("pId",participantId);
		q.setString("year",dateArray[0]);
		q.setString("month",dateArray[1]);
		q.setString("day",dateArray[2]);
		
		for(Object o : q.list())
			macIds.add(o.toString());

		return macIds;
	}
	
	//return JSON Array has wocket stats for each wocket of corresponding participant
	@SuppressWarnings("all")
	public static JSONArray getWocketsStatsData(int participantId,String[] dateArray,Session session)
	{
		JSONArray wktsJsonList = new JSONArray();//main JSON object has list of wocketJson
		JSONArray wcktFlagsList = new JSONArray();//wocket swapped flags
		SQLQuery q = null;
		//get disticnt mac_id for selected day
		ArrayList<String> macIds = getParticipnatMacIds(participantId,dateArray,session);
		//for each wocket get its data from wocket_stats table for selected day
		for(String macId:macIds)
		{
			List Swaplist = getSwappedTime(macId, dateArray, session);//check for entire day swap time
			
			String query = "SELECT Create_Date, Activity_Count, Wocket_Battery "+
										"FROM Wockets_Stats "+
										"WHERE Participant_Id =:pId "+
										"AND Mac_Id =:mac_Id "+
										"AND Create_Date >=:startTime "+
										"AND Create_Date <=:endTime "+
										"ORDER BY Create_Date ASC";
			
			JSONArray wktRecordJSONArr = new JSONArray();
			if(Swaplist.size()==0)//if there was no swap occurred for wocket on selected day
			{
				q = session.createSQLQuery(query);
				q.setInteger("pId",participantId);
				q.setString("mac_Id",macId);
				q.setString("startTime",dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]);
				q.setString("endTime",dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]+" "+"23:59:59");
				List list = q.list();
				String position = wocketPosition(macId, dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2], session);
				
				JSONObject wocketActivitySeries = new JSONObject();
				wocketActivitySeries.put("name",position+"("+macId+")");
				JSONArray activitydata = ChartUtility.getChartSeriesJSON(list,0,1);//get activity data by passing time and activity valueindices of list
				wocketActivitySeries.put("data", activitydata);
				wocketActivitySeries.put("id", position+"("+macId+")");//set each series unique Id as mac ID
				wktRecordJSONArr.add(wocketActivitySeries);
			}
			else
			{
				Map<String,List> wcktMap = new HashMap<String, List>();
				String startTime = dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2];
				for(int y=0; y<=Swaplist.size();y++)
				{
					String position = wocketPosition(macId, startTime, session);
					String endTime = "";
					if(y==Swaplist.size())
						endTime = dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]+" "+"23:59:59";
					else
						endTime = Swaplist.get(y).toString();
					q = session.createSQLQuery(query);
					q.setInteger("pId",participantId);
					q.setString("mac_Id",macId);
					q.setString("startTime",startTime);
					q.setString("endTime",endTime);
					String key = position+"("+macId+")";
					if(wcktMap.containsKey(key))
					{
						List list = wcktMap.get(key);
						List newList = q.list();
						list.addAll(newList);
						wcktMap.remove(key);
						wcktMap.put(key, list);
					}
					else
					{
						wcktMap.put(key,q.list());
					}
					startTime = endTime;
				}
				
				Iterator it = wcktMap.entrySet().iterator();
			    while (it.hasNext()) {
			        Map.Entry pairs = (Map.Entry)it.next();
			        JSONObject wocketActivitySeries = new JSONObject();
					wocketActivitySeries.put("name",pairs.getKey());
					JSONArray activitydata = ChartUtility.getChartSeriesJSON((List)pairs.getValue(),0,1);//get activity data by passing time and activity valueindices of list
					wocketActivitySeries.put("data", activitydata);
					wocketActivitySeries.put("id", pairs.getKey());//set each series unique Id as mac ID
					wktRecordJSONArr.add(wocketActivitySeries);
					}
			}
			
			JSONObject wocketBatterySeries = new JSONObject();
			wocketBatterySeries.put("name","Battery("+macId+")");
			JSONArray batteryData = ChartUtility.getChartSeriesJSON(getBatteryValue(participantId, macId, dateArray, session),0,1);//get activity data by passing time and battery valueindices of list 
			wocketBatterySeries.put("data", batteryData);
			wktRecordJSONArr.add(wocketBatterySeries);
			
			wktsJsonList.add(wktRecordJSONArr);
		}

		return wktsJsonList;
	}
	
	//get sensor position at start time
	@SuppressWarnings("all")
	public static String wocketPosition(String macId,String startTime,Session session)
	{
		SQLQuery q = session.createSQLQuery("SELECT Sensor_Placement " +
											"FROM Swapped_Sensor "+
											"WHERE Swapping_Id = (SELECT Swapping_Id FROM Swapping "+ 
																  "WHERE Swap_Time <=:startTime "+
																  "Order By Swap_Time Desc limit 1)"+
											"AND Mac_Id =:macId");
		q.setString("startTime", startTime);
		q.setString("macId",macId);
		List list = q.list();
		String position = "";
		if(list.size()!=0)
			position = list.get(0).toString();
		else
		{
//			q = session.createSQLQuery("SELECT Sensor_Placement " +
//										"FROM Swapped_Sensor "+
//										"WHERE Swapping_Id = (SELECT Swapping_Id FROM Swapping "+ 
//										"WHERE Swap_Time >=:startTime "+
//										"Order By Swap_Time ASC limit 1)"+
//										"AND Mac_Id =:macId");
			q = session.createSQLQuery("SELECT Sensor_Placement " +
										"FROM Swapped_Sensor "+
										"WHERE Swapping_Id IN (SELECT Swapping_Id FROM Swapping "+ 
										"WHERE Swap_Time >=:startTime "+
										"Order By Swap_Time ASC)"+
										"AND Mac_Id =:macId");
			q.setString("startTime", startTime);
			q.setString("macId",macId);
			List lis = q.list();
			position = lis.get(0).toString();
		}
		return position;
	}
	
	//get all swapped time for one day
	@SuppressWarnings("all")
	public static List getSwappedTime(String macId,String[] dateArray,Session session)
	{
		SQLQuery q = session .createSQLQuery("SELECT S.Swap_Time "+ 
											"FROM Swapping S INNER JOIN Swapped_Sensor SS "+
											"ON S.Swapping_Id = SS.Swapping_Id "+
											"WHERE Mac_ID =:macId "+
											"AND S.Swap_Time >=:startTime "+ 
											"AND S.Swap_Time <=:endTime "+
											"ORDER By S.Swap_Time ASC");
		q.setString("macId",macId);
		q.setString("startTime",dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]);
		q.setString("endTime",dateArray[0]+"-"+dateArray[1]+"-"+(Integer.parseInt(dateArray[2])+1));
		List list = q.list();
		return list;
	}
	
	//get Swapped Flags 
	@SuppressWarnings("all")	
	public static JSONArray getSwappedFlag(int participantId,String[] dateArray,Session session)
	{
		String qStr = "SELECT S.Swap_Time, SS.Sensor_Placement "+ 
				  "FROM Swapping S INNER JOIN Swapped_Sensor SS "+
				  "ON S.Swapping_Id = SS.Swapping_Id "+
				  "WHERE Mac_ID =:macId "+
				  "AND S.Swap_Time >=:startTime "+ 
				  "AND S.Swap_Time <=:endTime "+
				  "ORDER By S.Swap_Time ASC";

	ArrayList<String> macIds = getParticipnatMacIds(participantId,dateArray,session);
	JSONArray swappedFlagArray = new JSONArray();
	int nbrSwap = 1;
	int flagHeight = -50;
	for(String macId: macIds)//for each find all swapped time for selected day
	{
		//List Swaplist = getSwappedTime(macId, dateArray, session);
		SQLQuery q = session.createSQLQuery(qStr);
		q.setString("macId",macId);
		q.setString("startTime",dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]);
		q.setString("endTime",dateArray[0]+"-"+dateArray[1]+"-"+(Integer.parseInt(dateArray[2])+1));
		List Swaplist = q.list();
		
		JSONObject swappedFlag = new JSONObject();
		swappedFlag.put("type","flags");
		JSONArray swappedData = new JSONArray();
		for(int n=0;n<Swaplist.size();n++)
		{
			JSONObject data = new JSONObject();
			Object[] objects = (Object[])Swaplist.get(n); 
			String timeStr = objects[0].toString();
			data.put("x",ChartUtility.convertToUTC(timeStr));
			data.put("title","S-"+nbrSwap);
			data.put("text","Wocket-"+macId+": Swapped at "+timeStr+" to "+objects[1].toString()+" position");//text string show swapped detail
			swappedData.add(data);
			nbrSwap++;
		}
		swappedFlag.put("name","Swapped("+macId+")");
		swappedFlag.put("data",swappedData);
		swappedFlag.put("shape","flag");
		swappedFlag.put("fillColor","#FAC0F3");
		swappedFlag.put("stackDistance",20);
		if(flagHeight <= -150)
			flagHeight = -50;  //reset flag height to -50 if it become -150
		flagHeight += -50;
		swappedFlag.put("y", flagHeight);
		swappedFlagArray.add(swappedFlag);
	}

	return swappedFlagArray;
}
	
//get last swapped time of wocket since selected date
@SuppressWarnings("all")
public static String getLastTimeBeforeSwapped(String macId,String swappedTime,Session session)
{
		SQLQuery query = session.createSQLQuery("SELECT Create_Date "+
											 	"FROM Wockets_Stats "+
											 	"WHERE Mac_Id =:macId "+
											 	"AND Create_Date <=:time "+
											 	"Order By Create_Date Desc limit 1");
		query.setString("macId",macId);
		query.setString("time",swappedTime);
		List list = query.list();
		if(list.size()==0)
		{
			query = session.createSQLQuery("SELECT Create_Date "+
				 	"FROM Wockets_Stats "+
				 	"WHERE Mac_Id =:macId "+
				 	"AND Create_Date >=:time "+
				 	"Order By Create_Date ASC limit 1");
			query.setString("macId",macId);
			query.setString("time",swappedTime);
			list = query.list();
		}
		return list.get(0).toString();
	}
	
	//get battery data for wocket
@SuppressWarnings("all")
	public static List getBatteryValue(int participantId,String macId,String[] dateArray,Session session)
	{
		SQLQuery q = session.createSQLQuery("SELECT Create_Date, Wocket_Battery "+
											"FROM Wockets_Stats "+
											"WHERE Participant_Id =:pId "+
											"AND Mac_Id =:mac_Id "+
											"AND YEAR(Create_Date) =:year "+
											"AND MONTH(Create_Date) =:month "+
											"AND DAY(Create_Date) =:day "+
											"ORDER BY Create_Date ASC");
		q.setInteger("pId",participantId);
		q.setString("mac_Id",macId);
		q.setString("year",dateArray[0]);
		q.setString("month",dateArray[1]);
		q.setString("day",dateArray[2]);
		List list = q.list();
		return list;
	}
	
	//get Phone_Stats data
	@SuppressWarnings("all")
	public static JSONArray getPhoneStats(int participantId,String[] dateArray,Session session)
	{
		JSONArray phoneStats = new JSONArray();
		SQLQuery query = session.createSQLQuery("SELECT Create_Date, Phone_Battery, Main_Memory, SD_Memory "+
												"FROM Phone_Stats "+
												"WHERE Participant_Id =:pId "+
												"AND YEAR(Create_Date) =:year "+
												"AND MONTH(Create_Date) =:month "+
												"AND DAY(Create_Date) =:day "+
												"ORDER BY Create_Date ASC");
		query.setInteger("pId",participantId);
		query.setString("year",dateArray[0]);
		query.setString("month",dateArray[1]);
		query.setString("day",dateArray[2]);
		List list = query.list();
		//phone battery JSON object
		JSONObject PhoneBatterySeries = new JSONObject();
		PhoneBatterySeries.put("name","Phone-Battery");
		JSONArray batteryData = ChartUtility.getChartSeriesJSON(list,0,1);//get activity data by passing list and time and battery value indices in list
		PhoneBatterySeries.put("data", batteryData);
		phoneStats.add(PhoneBatterySeries);
		
		//phone Main memory JSON object
		JSONObject mainMemorySeries = new JSONObject();
		mainMemorySeries.put("name","Main-Memory");
		JSONArray mainMemoryData = ChartUtility.getChartSeriesJSON(list,0,2);//get activity data by passing list and time and main memory value indices in list
		mainMemorySeries.put("data", mainMemoryData);
		phoneStats.add(mainMemorySeries);
		
		//phone SD memory JSON object
		JSONObject SDMemorySeries = new JSONObject();
		SDMemorySeries.put("name","SD-Memory");
		JSONArray SDMemoryData = ChartUtility.getChartSeriesJSON(list,0,3);//get activity data by passing list and time and SD memory value indices in list
		SDMemorySeries.put("data", SDMemoryData);
		phoneStats.add(SDMemorySeries);
		
		return phoneStats;
	}
	
	//get Raw_Data_Stats
	@SuppressWarnings("all")
	public static JSONObject getRawDataStats(int participantId,String[] dateArray,Session session)
	{
		JSONObject rawDataStats = new JSONObject();
		SQLQuery query = session.createSQLQuery("SELECT Create_Time, Data_Size "+
												"FROM Raw_Data_Stats "+
												"WHERE Participant_Id =:pId "+
												"AND YEAR(Create_Time) =:year "+
												"AND MONTH(Create_Time) =:month "+
												"AND DAY(Create_Time) =:day "+
												"ORDER BY Create_Time ASC");
		query.setInteger("pId",participantId);
		query.setString("year",dateArray[0]);
		query.setString("month",dateArray[1]);
		query.setString("day",dateArray[2]);
		List list = query.list();
		
		rawDataStats.put("name","Raw-Data");
		JSONArray RawData = ChartUtility.getChartSeriesJSON(list,0,1);//get activity data by passing list and time and battery value indices in list
		rawDataStats.put("data", RawData);
		
		return rawDataStats;
	}
	
	//get SMS detail for selected date
	@SuppressWarnings("all")
	public static JSONObject getSMSMssgs(int participantId,String[] dateArray,Session session)
	{
		JSONObject smsObj = new JSONObject();
		smsObj.put("type","flags");
		smsObj.put("name","SMS");
		JSONArray dataList = new JSONArray();
		SQLQuery query = session.createSQLQuery("SELECT SMS_Id, Message_Time, Message "+
												"FROM Sms_Msgs "+
												"WHERE Participant_Id =:pId "+
												"AND Message_Time BETWEEN :startTime AND :endTime");
		query.setInteger("pId",participantId);
		query.setString("startTime",dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]);
		query.setString("endTime",dateArray[0]+"-"+dateArray[1]+"-"+(Integer.parseInt(dateArray[2])+1));
		List smsList = query.list();
		for(int i=0;i<smsList.size();i++)
		{
			Object[] objects = (Object[])smsList.get(i);
			JSONObject data = new JSONObject();
			data.put("x",ChartUtility.convertToUTC(objects[1].toString()));//sms time
			//data.put("title","SMS #"+objects[0].toString());//sms unique Id
			data.put("title","SMS #"+(i+1));//sms unique Id
			data.put("text",objects[2].toString());//sms message
			dataList.add(data);
		}
		smsObj.put("data",dataList);
		smsObj.put("width",50);//flsg width
		smsObj.put("y", -150);//distance from x-axis
		smsObj.put("fillColor","#77E8F7");

		return smsObj;
	}
	
	//get prompt detail
	@SuppressWarnings("all")
	public static JSONObject getPromptDetail(int participantId,String[] dateArray,Session session)
	{
		JSONObject promptObj = new JSONObject();
		promptObj.put("type","flags");
		promptObj.put("name","Prompt");
		JSONArray dataList = new JSONArray();

		SQLQuery query = session.createSQLQuery("SELECT Prompt_Id, Prompt_Type, Prompt_Time, Response_Time, Activity_Interval," +
												"Primary_Activity,Alternate_Activities "+
												"FROM PROMPTING "+
												"WHERE Participant_Id =:pId "+
												"AND Prompt_time BETWEEN :startTime AND :endTime");
		query.setInteger("pId", participantId);
		query.setString("startTime",dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]);
		query.setString("endTime",dateArray[0]+"-"+dateArray[1]+"-"+(Integer.parseInt(dateArray[2])+1));
		List list = query.list();
		for(int i=0; i<list.size();i++)
		{
			Object[] objects = (Object[])list.get(i);
			JSONObject data = new JSONObject();
			data.put("x",ChartUtility.convertToUTC(objects[2].toString()));
			String title = "P #"+(i+1);
			if(objects[3]==null)
				title += ":NR";
			data.put("title",title);//sms unique Id
			String text = "Prompt-Type:"+objects[1].toString()+"<br/>"+
						  "Prompt-Time:"+objects[2].toString()+"<br/>"+
						  "Response-Time:"+objects[3]+"<br/>"+
						  "Activity-Intv.:"+objects[4]+"<br/>"+
						  "Primary-Act.:"+objects[5]+"<br/>"+
						  "Alternate-Act.:"+objects[6];

			data.put("text",text);//sms message
			dataList.add(data);
		}
		promptObj.put("data",dataList);
		promptObj.put("width",50);//flsg width
		promptObj.put("y", -50);//distance from x-axis
		promptObj.put("fillColor","#C29BA5");
		return promptObj;
	}
	
//get Hidden series to make Y-axis fixed size
	public static JSONObject getHiddenSeries(String[] dateArray)
	{
		JSONObject hiddenSeries = new JSONObject();
		hiddenSeries.put("id","hidden");
		JSONArray dataList = new JSONArray();
		JSONArray data  = new JSONArray();
		String date = dateArray[0]+"-"+dateArray[1]+"-"+dateArray[2]+" "+"00:00:01";
		data.add(ChartUtility.convertToUTC(date));
		data.add(20000);
		dataList.add(data);
		hiddenSeries.put("data",dataList);
		hiddenSeries.put("showInLegend",false);

		return hiddenSeries;
	}

}
