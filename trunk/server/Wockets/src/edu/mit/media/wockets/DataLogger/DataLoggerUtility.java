package edu.mit.media.wockets.DataLogger;

import java.io.File;
import java.io.IOException;
import java.util.List;

import javax.xml.XMLConstants;
import javax.xml.transform.sax.SAXSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;

import org.hibernate.Query;
import org.hibernate.Session;
import org.hibernate.Transaction;
import org.springframework.format.annotation.DateTimeFormat;
import org.xml.sax.SAXException;

import com.ibm.icu.text.SimpleDateFormat;

import edu.mit.media.wockets.DataLogger.DataLoggerBean.*;
import edu.mit.media.wockets.utility.HibernateSession;

public class DataLoggerUtility {
	
	public static Schema loadXsdSchema(String name) 
	{
		Schema schema = null;
		try {
		      String language = XMLConstants.W3C_XML_SCHEMA_NS_URI;
		      SchemaFactory factory = SchemaFactory.newInstance(language);
		      schema = factory.newSchema(new File(name));
		    } catch (Exception e) {
		      System.out.println(e.toString());
		    }
		 return schema;
	}
	
	public static boolean isValidate(String xsdFilePath, SAXSource source)
	{
		boolean result = true;
		Schema xsdSchema = loadXsdSchema(xsdFilePath);
		Validator validator = xsdSchema.newValidator();
		try{
		validator.validate(source);
		}
		catch(SAXException saxEx)
		{
			result = false;
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		return result;
	}
	
	//insert all data to database
	public static void insertDataToDB(DataContainer dataContainer)
	{
		int rowNbr = 0;//int to check number of records
		Session session = HibernateSession.getSession();
		Transaction tx = session.beginTransaction();
		Query query;
		//insert prompting record
		List<Prompting> pList = dataContainer.getPromptingList();
		if(pList != null)
		{
			for(int i=0; i<pList.size(); i++)
			{
				Prompting prompt = pList.get(i);
				pList.set(i,null);
				if(!pList.contains(prompt))
				{
					query = session.createQuery("FROM Prompting prompting WHERE Participant_Id =:pId AND Prompt_type =:promptType AND Prompt_Time =:promptTime " +
									 "AND Response_Time =:responseTime AND Activity_Interval =:activityInterval AND Primary_Activity =:primaryAct " +
									 "AND Alternate_Activities=:alternateAct");
				
					query.setInteger("pId",prompt.getParticipantId());
					query.setString("promptType",prompt.getPromptType());
					query.setString("promptTime",prompt.getPromptTime());
					query.setString("responseTime",prompt.getResponseTime());
					query.setInteger("activityInterval",prompt.getActivityInterval());
					query.setString("primaryAct",prompt.getPrimaryActivity());
					query.setString("alternateAct",prompt.getAlternateActivity());
					if(!exists(query))
					{
						session.save(prompt);
						rowNbr++;
						checkFirstLevelCache(rowNbr, session);
					}
				}
			}
		}
		//insert into PhoneStats
		List<PhoneStats> psList = dataContainer.getPhoneStatsList();
		if(psList != null)
		{
			for(PhoneStats ps:dataContainer.getPhoneStatsList())
			{
				query = session.createQuery("FROM PhoneStats phonestats WHERE Participant_Id =:pId AND Create_Date =:createDate AND Phone_Battery =:phoneBattery "+
					 "AND Main_Memory=:mainMemory AND SD_Memory=:sdMemory");


				query.setInteger("pId",ps.getParticipantId());
				query.setString("createDate",ps.getCreateDate());
				query.setInteger("phoneBattery",ps.getPhoneBattery());
				query.setInteger("mainMemory",ps.getMainMemo());
				query.setInteger("sdMemory",ps.getSdMemo());
				if(!exists(query))
				{
					session.save(ps);
					rowNbr++;
					checkFirstLevelCache(rowNbr, session);
				}
			}
		}
		//insert WocketStats
		if(dataContainer.getWocketStateList() != null)
		{
			for(WocketStats ws: dataContainer.getWocketStateList())
			{
				query = session.createQuery("FROM WocketStats wocketStats WHERE Participant_Id =:pId AND Mac_Id =:macId AND Create_Date =:createDate "+
					 "AND Activity_Count=:activityCount AND Wocket_Battery=:wocketBattery AND Transmitted_Bytes=:transmittedByte AND Received_Bytes=:receivedBytes");

				query.setInteger("pId",ws.getParticipantId());
				query.setString("macId", ws.getMacId());
				query.setString("createDate",ws.getCreateDate());
				query.setInteger("activityCount",ws.getActivityCount());
				query.setInteger("wocketBattery",ws.getWocketBattery());
				query.setInteger("transmittedByte",ws.getTransmittedByte());
				query.setInteger("receivedBytes",ws.getReceivedBytes());
				if(!exists(query))
				{
					session.save(ws);
					rowNbr++;
					checkFirstLevelCache(rowNbr, session);
				}
			}
		}
		//insert swapping and SwappedSensor record
		if(dataContainer.getSwappingList() != null)
		{
			for(Swapping s: dataContainer.getSwappingList())
			{
				query = session.createQuery("FROM Swapping swapping WHERE Participant_Id =:pId AND Swap_Time =:swapTime AND Swap_event =:swapEvent "+
					 					"AND Restarted_Event=:restartedEvent AND LocationChanged_Event=:loctChangedevent");

				query.setInteger("pId",s.getParticipantId());
				query.setString("swapTime", s.getSwapTime());
				query.setString("swapEvent",s.getSwapEvent());
				query.setString("restartedEvent",s.getRestartedEvent());
				query.setString("loctChangedevent",s.getLoctChangedevent());
				if(!exists(query))
				{
					session.save(s);
					rowNbr++;

					for(SwappedSensor sws:s.getSwappedSensor())
					{
//					query = session.createSQLQuery("SELECT S.Participant_Id FROM SWAPPING S INNER JOIN SWAPPED_SENSOR SS "+
//											"ON S.Swapping_Id = SS.Swapping_Id " +
//											"WHERE S.Participant_Id =:pId AND S.Swap_Time =:swapTime AND S.Swap_event =:swapEvent "+
//											"AND S.Restarted_Event=:restartedEvent AND S.LocationChanged_Event=:loctChangedevent "+
//											"AND SS.Mac_Id=:macId AND SS.Sensor_Placement=:sensorPlacement");
//				query.setInteger("pId",s.getParticipantId());
//				query.setString("swapTime",s.getSwapTime());
//				query.setString("swapEvent",s.getSwapEvent());
//				query.setString("restartedEvent",s.getRestartedEvent());
//				query.setString("loctChangedevent",s.getLoctChangedevent());
//				query.setString("macId",sws.getMacId());
//				query.setString("sensorPlacement", sws.getSensorPlacement());
				session.flush();
				session.clear();
				session.evict(sws);
				session.evict(s);

						sws.setSwappingId(s.getSwappingId());
						session.save(sws);
						rowNbr++;
						checkFirstLevelCache(rowNbr, session);
					}
				}
				checkFirstLevelCache(rowNbr, session);
			}
		}
		
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
		//insert some notes
		if(dataContainer.getSomeNotes()!=null)
		{
			for(Note note : dataContainer.getSomeNotes())
			{
				query = session.createSQLQuery("SELECT * FROM Note WHERE Participant_Id =:pId AND Start_Time =:sTime AND Note =:note");

				query.setInteger("pId",note.getParticipantID());
				query.setString("sTime",sdf.format(note.getStartTime()));
				//not consider End_Time for duplicate entry because getting problem because of IS NULL in database
//				if(note.getEndTime()!=null)
//					query.setString("eTime",sdf.format(note.getEndTime()));
//				else
//					query.setString("eTime",null);
				query.setString("note",note.getNote());
				if(!exists(query))
				{
					session.save(note);
				}
				rowNbr++;
				checkFirstLevelCache(rowNbr, session);
			}
		}
		
		//insert Heart Rate 
		if(dataContainer.getSomeHRData() != null)
		{
			for(HRData hr : dataContainer.getSomeHRData())
			{
				query = session.createQuery("FROM HRData hrdata WHERE Participant_Id =:pId AND Create_Time =:cTime AND HeartRate =:hr AND Sensor_Battery =:battery");
				query.setInteger("pId",hr.getParticipantID());
				query.setString("cTime",sdf.format(hr.getCreateTime()));
				query.setInteger("hr",hr.getHeartRate());
				query.setInteger("battery",hr.getBattery());
				if(!exists(query))
				{
					session.save(hr);
				}
				rowNbr++;
				checkFirstLevelCache(rowNbr, session);
			}
		}
		
		//insert DataUploadEvent
		if(dataContainer.getSomeRawUploads() != null)
		{
			for(DataUploadEvent due : dataContainer.getSomeRawUploads())
			{
//				query = session.createQuery("FROM DataUploadEvent dataUploadEvent WHERE Participant_Id =:pId AND Start_Upload_Time =:sut " +
//											"AND End_Upload_Time =:eut AND IS_Successful =:isSucc AND Start_Data_Time =:sdt AND End_Data_Time =:edt " +
//											"AND File_Name =:fName AND File_Size =:fSize AND Note=:note");
				query = session.createSQLQuery("SELECT * FROM Data_Upload_Event WHERE Participant_Id =:pId AND Start_Upload_Time =:sut " +
											"AND End_Upload_Time =:eut AND IS_Successful =:isSucc AND Start_Data_Time =:sdt AND End_Data_Time =:edt " +
											"AND File_Name =:fName AND File_Size =:fSize AND Note=:note");
				query.setInteger("pId",due.getParticipantID());
				query.setString("sut",sdf.format(due.getStartUploadTime()));
				query.setString("eut",due.getEndUploadTime()!=null?sdf.format(due.getEndUploadTime()):null);
				query.setCharacter("isSucc", due.getResultStatus()==true ?'1':'0');
				query.setString("sdt",sdf.format(due.getStartDataTime()));
				query.setString("edt",sdf.format(due.getEndDataTime()));
				query.setString("fName",due.getFileName());
				query.setInteger("fSize", due.getFileSize());
				query.setString("note",due.getNote());
				if(!exists(query))
				{
					session.save(due);
				}
				rowNbr++;
				checkFirstLevelCache(rowNbr, session);
			}
		}
		
		tx.commit();
		HibernateSession.sessionClose(session);

	}
	
	//flush and clear session cache once it reached to 20
	public static void checkFirstLevelCache(int rowNbr, Session session)
	{
		if(rowNbr%20==0)
		{
			session.flush();
			session.clear();
		}
	}
	
	//check object exist in database or not
	public static Boolean exists(Query query) {
		
	    return (query.list().size() > 0);
	}

	

}
