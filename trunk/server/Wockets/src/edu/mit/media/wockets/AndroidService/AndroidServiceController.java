/**
 * Created By Salim Khan
 */
package edu.mit.media.wockets.AndroidService;

import java.io.IOException;
import java.util.List;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import net.sf.json.JSONArray;
import net.sf.json.JSONObject;

import org.hibernate.SQLQuery;
import org.hibernate.Session;

import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;


import edu.mit.media.wockets.utility.HibernateSession;

@Controller
public class AndroidServiceController {

	//return Participant_Id based on Phone IMEI number
	@RequestMapping(value="/android/getParticipantId.html", method=RequestMethod.GET)
	public void androidGetParticipantId(HttpServletRequest request, HttpServletResponse response)
	{
	
		String pId = null;
		String imei = request.getParameter("imei");
		if(imei!=null)
		{
			Session session = HibernateSession.getSession();
			SQLQuery query = session.createSQLQuery("SELECT Participant_Id FROM Participant_Phone " +
													"WHERE IMEI =:imei");
			query.setString("imei",imei);
			List list = query.list();
			if(list.size() == 1)
			{
				pId = list.get(0).toString();
				System.out.println(pId);
				try {response.getWriter().print(pId);}
				catch (IOException e) {e.printStackTrace();}
			}
			else
			{
				try{response.sendError(response.SC_BAD_REQUEST,"No record found for imei:"+imei);}
				catch(Exception e){e.printStackTrace();}
			}
		}
		
		else
		{
			try{response.sendError(response.SC_BAD_REQUEST,"imei parameter not found.");}
			catch(Exception e){e.printStackTrace();}
		}
	}
	
	//return all active wockets detail based on participant Id
	@RequestMapping(value="/android/getWocketsDetail.html",method=RequestMethod.GET)
	public void androidGetWocketsDetail(HttpServletRequest request, HttpServletResponse response)
	{
		int pId;
		try{
		pId = Integer.parseInt(request.getParameter("pId"));//get participant_Id from request
		Session session = HibernateSession.getSession();
		SQLQuery query = session.createSQLQuery("SELECT W.Mac_Id,W.Set_Color,W.Hardware_Version,W.FirmWare_Version,W.Printed_Id " +
												"FROM Wockets W INNER JOIN Participant_Wockets PW " +
												"ON W.Mac_Id = PW.Mac_Id " +
												"WHERE PW.Participant_Id =:pId");
		query.setInteger("pId",pId);
		List list = query.list();
		if(list.size()!=0)
		{
			JSONArray wocketList = new JSONArray();
			for(int i=0; i<list.size();i++)
			{
				Object[] wocket = (Object[])list.get(i);
				JSONObject wocketJSON = new JSONObject();
				wocketJSON.put("mac_id",wocket[0]);
				wocketJSON.put("color",wocket[1]);
				wocketJSON.put("hardware_version",wocket[2]);
				wocketJSON.put("firmware_version",wocket[3]);
				wocketJSON.put("printed_id",wocket[4]);
				
				wocketList.add(wocketJSON);
			}
			JSONObject wocketJSONObj = new JSONObject();
			wocketJSONObj.put("wockets",wocketList);
			response.setContentType("application/x-json");
			response.getWriter().print(wocketJSONObj);
		}
		else
		{
			response.sendError(response.SC_BAD_REQUEST,"No record found for Participant_Id="+pId);
		}
		}
		catch(NumberFormatException nEx)
		{
			try{response.sendError(response.SC_BAD_REQUEST,"Illegal Participant_Id expected integer.");}
			catch(Exception e){e.printStackTrace();}
		}
		catch(IOException ioE)
		{
			try{response.sendError(response.SC_BAD_REQUEST,"I/O Exception occurred.");}
			catch(Exception e){e.printStackTrace();}
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		
	}
}
