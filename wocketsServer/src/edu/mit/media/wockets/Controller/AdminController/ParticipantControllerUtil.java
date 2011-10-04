/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Controller.AdminController;


import java.util.List;

import javax.servlet.http.HttpServletRequest;

import net.sf.json.JSONArray;
import net.sf.json.JSONObject;

import org.hibernate.Query;
import org.hibernate.SQLQuery;
import org.hibernate.Session;

import com.ibm.icu.util.StringTokenizer;

import edu.mit.media.wockets.Beans.ParticipantPhone;
import edu.mit.media.wockets.Beans.ParticipantSim;
import edu.mit.media.wockets.Beans.ParticipantStudy;
import edu.mit.media.wockets.Beans.ParticipantWocket;
import edu.mit.media.wockets.utility.HibernateSession;

public class ParticipantControllerUtil {
	
	//enroll participant into study and add row to PARTICIPANT_STUDY table
	public static void enrollInStudy(HttpServletRequest req,Session session, int participantId)
	{
		StringTokenizer strTkz = new StringTokenizer(req.getParameter("concatStudyStr"),"|");//has a slected study detail seperated by '|'
		while(strTkz.hasMoreTokens())
		{
			String stdDetails = strTkz.nextToken();
			String[] detail = stdDetails.split(":");//each stdDetail has study Id, start date and end date seperated by '?:' symbols
			ParticipantStudy pStudy = new ParticipantStudy();
			pStudy.setParticipantId(participantId);
			pStudy.setStudyId(detail[0]);
			pStudy.setStartDate(detail[1]);
			pStudy.setEndDate(detail[2]);
			session.save(pStudy);
			pStudy = null;
		}
		session.flush();
	}
	
	//Assign Phone to participant and add row to PARTICIPANT_PHONE table
	public static void assignPhone(HttpServletRequest req,Session session, int participantId)
	{
		//set Inactive if any record exist in PARTICIPANT_PHONE table of participant
		Query q = session.createSQLQuery("UPDATE PARTICIPANT_PHONE SET Active_Status=:char WHERE Participant_Id=:pId");
		q.setCharacter("char",'0');
		q.setInteger("pId",participantId);
		q.executeUpdate();
		
		//Insert new record in PARTICIPANT_PHONE table
		ParticipantPhone pPhone = new ParticipantPhone();
		pPhone.setParticipantId(participantId);
		pPhone.setImei(req.getParameter("IMEI"));
		pPhone.setActiveStatus('1');
		pPhone.setInactiveReason("N/A");
		session.save(pPhone);
		pPhone = null;
	}
	
	//Assign SIM to participant and add row to PARTICIPANT_SIM table
	public static void assignSim(HttpServletRequest req,Session session, int participantId)
	{
		//set Inactive if any record exist in PARTICIPANT_SIM table of participant
		Query q = session.createSQLQuery("UPDATE PARTICIPANT_SIM SET Active_Status=:char WHERE Participant_Id=:pId");
		q.setCharacter("char",'0');
		q.setInteger("pId",participantId);
		q.executeUpdate();
		
		ParticipantSim pSim = new ParticipantSim();
		pSim.setParticipantId(participantId);
		pSim.setPhoneNbr(req.getParameter("phoneNbr"));
		pSim.setActiveStatus('1');
		session.save(pSim);
		pSim = null;
	}
	
	
	
	//Assign Wocket to participant add row to PARTICIPANT_WOCKETS table and update isAssigned status in Wocket table
	public static void assignWocket(HttpServletRequest req,Session session, int participantId)
	{	
		String concatWocketId = req.getParameter("wocketConcatStr");//String has concat wocket Id's seperated by '|'
		StringTokenizer strToken = new StringTokenizer(concatWocketId,"|");

		Query q = null;
		String wocketId = null;
		while(strToken.hasMoreTokens())
		{
			ParticipantWocket pWocket = new ParticipantWocket();
			pWocket.setParticipantId(participantId);
			wocketId = strToken.nextToken();
			pWocket.setWocketId(wocketId);
			session.save(pWocket);
			q = session.createSQLQuery("UPDATE WOCKETS SET IsAssigned =:char WHERE Mac_Id =:macId");
			q.setCharacter("char",'1');
			q.setString("macId", wocketId);
			q.executeUpdate();
		}
}
	
	//change Phone status to Assigned in PHONE table
	public static void updatePhoneTable(HttpServletRequest req,Session session)
	{
		Query q = session.createSQLQuery("UPDATE PHONE SET IsAssigned =:char WHERE IMEI =:imei");
		q.setCharacter("char",'1');
		q.setString("imei",req.getParameter("IMEI"));
		q.executeUpdate();
	}
	
	//change Sim card status to Assigned in SIMCARDS table
	public static void updateSimTable(HttpServletRequest req,Session session)
	{
		Query q = session.createSQLQuery("UPDATE SIMCARDS SET IsAssigned =:char WHERE Phone_Number =:pNbr");
		q.setCharacter("char",'1');
		q.setString("pNbr",req.getParameter("phoneNbr"));
		q.executeUpdate();
		session.flush();
	}
	
	//Return JSON object of Participant Assigned Phone
	public static JSONObject getAssignedPhone(int pId)
	{
		Session session = HibernateSession.getSession();
		SQLQuery q = session.createSQLQuery("SELECT Phone.*,Participant_Phone.Active_Status,Participant_Phone.Reason_of_Change from Phone INNER JOIN Participant_Phone ON Phone.IMEI = Participant_Phone.IMEI where Participant_Phone.Participant_Id=:pId");
		q.setInteger("pId",pId);
		List list = q.list();
		HibernateSession.sessionClose(session);

		JSONObject jObj =new JSONObject();// main JSON object
		JSONArray rowListObj=new JSONArray();//List of phone JSON object

		for(int i=0 ;i<list.size();i++)
		{	
			Object[] objectList = (Object[])list.get(i);
			JSONObject rowObj =new JSONObject();// JSON object for each phone
			rowObj.put("id",i);					//unique Id for each row object
			JSONArray rowData=new JSONArray();//data JSON object for each phone
			rowData.add(objectList[0].toString());
			rowData.add(objectList[1].toString());
			rowData.add(objectList[2].toString());
			rowData.add(objectList[3].toString());
			rowData.add(objectList[4].toString());
			if(objectList[6].toString().equals("1"))
				rowData.add("Active");
			else
				rowData.add("Inactive");
			rowData.add(objectList[7].toString());

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
         }
		jObj.put("rows",rowListObj);
		return jObj;
	}
	
	//Assign new Phone to existing participant
	public static void assignNewPhone(int pId,HttpServletRequest request)
	{
		Session session = HibernateSession.getSession();
		/***********************
		 * make all phone as inactive 
		 * because participant can have only one active phone at a time
		 **************************/
		SQLQuery q = session.createSQLQuery("UPDATE PARTICIPANT_PHONE SET Active_Status =:char, Reason_of_Change =:reason WHERE Active_Status ='1' AND Participant_Id=:pId");
		q.setCharacter("char",'0');
		q.setString("reason",request.getParameter("reason"));
		q.setInteger("pId",pId);
		q.executeUpdate();
		
		//Add new record to PARTICIPANT_PHONE table
		ParticipantPhone pPh = new ParticipantPhone();
		pPh.setActiveStatus('1');
		pPh.setParticipantId(pId);
		pPh.setImei(request.getParameter("IMEI"));
		pPh.setInactiveReason("N/A");
		session.save(pPh);
		updatePhoneTable(request, session);
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
	}
	
	
	//***********Manage Sim card********************
	
	//Return JSON object of Participant Assigned Sim
	public static JSONObject getAssignedSim(int pId)
	{
		Session session = HibernateSession.getSession();
		SQLQuery q = session.createSQLQuery("SELECT Simcards.*,Participant_Sim.Active_Status,Participant_Sim.Reason_of_Change from Simcards " +
				                             "INNER JOIN Participant_Sim ON Simcards.Phone_Number = Participant_Sim.Phone_Number " +
				                             "WHERE Participant_Sim.Participant_Id=:pId");
		q.setInteger("pId",pId);
		List list = q.list();
		HibernateSession.sessionClose(session);

		JSONObject jObj =new JSONObject();// main JSON object
		JSONArray rowListObj=new JSONArray();//List of sim JSON object

		for(int i=0 ;i<list.size();i++)
		{	
			Object[] objectList = (Object[])list.get(i);
			JSONObject rowObj =new JSONObject();// JSON object for each sim
			rowObj.put("id",i);					//unique Id for each row object
			JSONArray rowData=new JSONArray();//data JSON object for each sim
			rowData.add(objectList[0].toString());
			rowData.add(objectList[1].toString());
			rowData.add(objectList[2].toString());
			rowData.add(objectList[3].toString());
			if(objectList[5].toString().equals("1"))
				rowData.add("Active");
			else
				rowData.add("Inactive");
			if(objectList[6]==null)
				rowData.add("N/A");//null means its active sim hence set it as N/A
			else
				rowData.add(objectList[6].toString());

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
         }
		jObj.put("rows",rowListObj);
		return jObj;
	}
	
	//Assign new Sim to existing participant
	public static void assignNewSim(int pId,HttpServletRequest request)
	{
		Session session = HibernateSession.getSession();
		/***********************
		 * make all phone as inactive 
		 * because participant can have only one active phone at a time
		 **************************/
		SQLQuery q = session.createSQLQuery("UPDATE PARTICIPANT_SIM SET Active_Status =:char, Reason_of_Change =:reason WHERE Active_Status ='1' AND Participant_Id=:pId");
		q.setCharacter("char",'0');
		q.setString("reason",request.getParameter("reason"));
		q.setInteger("pId",pId);
		q.executeUpdate();
		
		//Add new record to PARTICIPANT_PHONE table
		ParticipantSim pSim = new ParticipantSim();
		pSim.setActiveStatus('1');
		pSim.setParticipantId(pId);
		pSim.setPhoneNbr(request.getParameter("phoneNbr"));
		pSim.setInactiveReason("N/A");
		session.save(pSim);
		updateSimTable(request, session);
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
	}
	
	//********Manage Wockets********************
	//return assigned wockets JSON object
	public static JSONObject getAssignedWocket(int pId)
	{
		Session session = HibernateSession.getSession();
		SQLQuery q = session.createSQLQuery("SELECT Wockets.* from Wockets " +
				                             "INNER JOIN Participant_Wockets ON Wockets.Mac_Id = Participant_Wockets.Mac_Id " +
				                             "WHERE Participant_Wockets.Participant_Id=:pId");
		q.setInteger("pId",pId);
		List list = q.list();
		HibernateSession.sessionClose(session);

		JSONObject jObj =new JSONObject();// main JSON object
		JSONArray rowListObj=new JSONArray();//List of sim JSON object

		for(int i=0 ;i<list.size();i++)
		{	
			Object[] objectList = (Object[])list.get(i);
			JSONObject rowObj =new JSONObject();// JSON object for each sim
			rowObj.put("id",i);					//unique Id for each row object
			JSONArray rowData=new JSONArray();//data JSON object for each sim
			rowData.add(objectList[0].toString());
			rowData.add(objectList[1].toString());
			rowData.add(objectList[2].toString());
			rowData.add(objectList[3].toString());
			rowData.add(objectList[4].toString());
			rowData.add(objectList[5].toString());

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
         }
		jObj.put("rows",rowListObj);
		return jObj;
	}
	
	
	

}
