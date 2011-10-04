package edu.mit.media.wockets.Controller.AdminController;

import java.io.IOException;
import java.util.List;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import net.sf.json.JSONArray;
import net.sf.json.JSONObject;

import org.hibernate.Query;
import org.hibernate.Session;
import org.springframework.stereotype.Controller;
import org.springframework.validation.BindingResult;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.servlet.ModelAndView;

import edu.mit.media.wockets.Beans.Participant;
import edu.mit.media.wockets.Beans.ParticipantPhone;
import edu.mit.media.wockets.Beans.Phone;
import edu.mit.media.wockets.Beans.Sim;
import edu.mit.media.wockets.Beans.Wocket;
import edu.mit.media.wockets.utility.HibernateSession;

@Controller
public class AdminParticipantController {
	
	//Return Participant Directory page
	@RequestMapping(value="/participantDirectory.html",method=RequestMethod.GET)
	public ModelAndView partDirectory(HttpServletRequest request)
	{
		/*****Use queryParticipant for updating selected participant from participant grid****
		********Setting it to null whenever participant directory page call****/
		request.getSession().setAttribute("queryParticipant",null);
		return new ModelAndView("admin-jsp/ParticipantDirectory");
	}

	//Return JSON object of participant List for dhtmlx grid
	@RequestMapping(value="/getParticipantDirectory.html",method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getPartDirectory(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Participant");
		
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<Participant> pList = (List<Participant>)list;
		JSONObject jObj =new JSONObject();// main JSON object
		JSONArray rowListObj=new JSONArray();// list of participant
		int i = 1;
		for(Participant p: pList)
		{	
			JSONObject rowObj =new JSONObject();//rowObj JSON object for each participant
			rowObj.put("id",i);
			JSONArray rowData=new JSONArray();// data JSON object for each participant
			rowData.add(p.getParticipant_Id());
			rowData.add(p.getfName());
			rowData.add(p.getlName());
			rowData.add(p.getGender());
			rowData.add(p.getEmail());
			if(p.getActiveStatus()=='1')
				rowData.add("Active");
			else
				rowData.add("Inactive");

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
			i++;
		}
		jObj.put("rows",rowListObj);
		res.setContentType("application/x-json");//set response type to JSON
		try {
			res.getWriter().print(jObj);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	

	//****************Registering New Participant section*************************************************
	
	//Return JSON object of all avilable phone List for dhtmlx grid
	@RequestMapping(value="/getAvailPhoneDirectory.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getAvailablePhoneList(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Phone WHERE IsAssigned=:char");
		q.setCharacter("char",'0');
		
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<Phone> phoneList = (List<Phone>)list;
		JSONObject jObj =new JSONObject();// main JSON object
		JSONArray rowListObj=new JSONArray();//List of phone JSON object
		int i = 1;
		for(Phone p: phoneList)
		{	
			JSONObject rowObj =new JSONObject();// JSON object for each phone
			rowObj.put("id",i);					//unique Id for each row object
			JSONArray rowData=new JSONArray();//data JSON object for each phone
			rowData.add(p.getIMEI());
			rowData.add(p.getPhoneModel());
			rowData.add(p.getPlatform());
			rowData.add(p.getOSVersion());
			rowData.add(p.getAppVersion());
			if(p.getIsAssigned()=='1')
				rowData.add("Assigned");
			else
				rowData.add("Not Assigned");

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
			i++;
		}
		jObj.put("rows",rowListObj);
		res.setContentType("application/x-json");
		try {res.getWriter().print(jObj);
		} catch (IOException e) {
			e.printStackTrace();}
	}
	
	//Return JSON object of all avilable Sim cards List for dhtmlx grid
	@RequestMapping(value="/getAvailableSimcardList.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getAvailableSimcardsList(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Sim WHERE IsAssigned=:char");
		q.setCharacter("char",'0');
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<Sim> simList = (List<Sim>)list;
		JSONObject jObj =new JSONObject();
		JSONArray rowListObj=new JSONArray();
		int i = 1;
		for(Sim s: simList)
		{	
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);
			JSONArray rowData=new JSONArray();
			rowData.add(s.getPhoneNbr());
			rowData.add(s.getCarrier());
			rowData.add(s.getContractExpDate());
			if(s.getIsAssigned()=='1')
				rowData.add("Assigned");
			else
				rowData.add("Not Assigned");
			rowData.add(s.getNotes());

			
			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
			i++;
		}
		jObj.put("rows",rowListObj);
		res.setContentType("application/x-json");
		try {res.getWriter().print(jObj);}
		catch (IOException e) {e.printStackTrace();}
	}
	
	//Return JSON object of all avilable wocket List for dhtmlx grid
	@RequestMapping(value="/getAvailableWocketList.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getAvailableWocketList(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Wocket WHERE IsAssigned=:char");
		q.setCharacter("char",'0');
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<Wocket> wocketList = (List<Wocket>)list;
		JSONObject jObj =new JSONObject();
		JSONArray rowListObj=new JSONArray();
		int i = 1;
		for(Wocket w: wocketList)
		{	
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);
			JSONArray rowData=new JSONArray();
			rowData.add(w.getWocketId());
			rowData.add(w.getColorSet());
			rowData.add(w.getHardwareVersion());
			rowData.add(w.getFirmwareVersion());
			rowData.add(w.getPrinted_Id());
			if(w.getIsAssigned()=='1')
				rowData.add("Assigned");
			else
				rowData.add("Not Assigned");
			rowData.add(w.getNotes());

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
			i++;
		}
		jObj.put("rows",rowListObj);
		res.setContentType("application/x-json");
		try {res.getWriter().print(jObj);}
		catch (IOException e) {e.printStackTrace();}
	}
	
	//return new Participant form
	@RequestMapping(value="/newParticipant.html", method= RequestMethod.GET)
	public ModelAndView newParticipantForm()
	{
		return new ModelAndView("admin-jsp/NewParticipant","participant",new Participant());
	}
	
	//submit new Participant
	@RequestMapping(value="/registerNewParticipant.html",method= RequestMethod.POST)
	public ModelAndView submitNewParticipant(@ModelAttribute("participant") Participant participant,HttpServletRequest request)
	{
		String enrollStatus = request.getParameter("enrollRadio");//shows participant is enrolled or not
		Session session = HibernateSession.getSession();
		if(enrollStatus.equals("yes"))
			participant.setActiveStatus('1');
		else
			participant.setActiveStatus('0');
		session.save(participant);
		session.flush();
		
		if(enrollStatus.equals("yes"))
		{
			//enroll participant into study
			ParticipantControllerUtil.enrollInStudy(request, session, participant.getParticipant_Id());
			//assign phone to participant
			ParticipantControllerUtil.assignPhone(request, session, participant.getParticipant_Id());
			//assign SIM to participant
			ParticipantControllerUtil.assignSim(request, session, participant.getParticipant_Id());
			//update PHONE table set assigned phone IsAssigned status as Assigned
			ParticipantControllerUtil.updatePhoneTable(request, session);
			//update SIMCARDS table set assigned simcard IsAssigned status as Assigned
			ParticipantControllerUtil.updateSimTable(request, session);
			//Assign wocket and update status of Wocket to assigned
			ParticipantControllerUtil.assignWocket(request, session, participant.getParticipant_Id());
		}
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
		return new ModelAndView("admin-jsp/RegisterParticipant","participant",participant);
	}
	
	//******************Manage Existing Participant*************************************
	
	//Manage participant page
	@RequestMapping(value="/manageParticipant.html", method=RequestMethod.GET)
	public ModelAndView participantMang(HttpServletRequest req)
	{
		int pId = Integer.parseInt(req.getParameter("pId"));
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("FROM Participant WHERE Participant_Id =:pId");
		q.setInteger("pId",pId);
		@SuppressWarnings("unchecked")
		List<Participant> pList = (List<Participant>)q.list();
		Participant p = pList.get(0);
		//********set participant into session for further use********
		req.getSession().setAttribute("queryParticipant",p);
		return new ModelAndView("admin-jsp/ManageParticipant","participant",p);
	}
	
	
	//Update personal Info
	@RequestMapping(value="/updatePartPersonalInfo.html",method=RequestMethod.GET)
	public ModelAndView updatePersonalInfo(@ModelAttribute("participant") Participant participant,HttpServletRequest request)
	{
		Session session = HibernateSession.getSession();
		session.update(participant);
		session.flush();
		HibernateSession.sessionClose(session);
		return new ModelAndView("admin-jsp/ManageParticipant","participant",participant);
	}
	
	
	//dhtmlx request to get JSON for assigned phone
	@RequestMapping(value="/getPartAssignedPhone.html", method=RequestMethod.GET)
	public void getParticipantAssignedPhone(HttpServletRequest request,HttpServletResponse response)
	{
		//Get Participant from Http Session which is set earlier
		int pId = ((Participant)request.getSession().getAttribute("queryParticipant")).getParticipant_Id();
		JSONObject jObject = ParticipantControllerUtil.getAssignedPhone(pId);
		response.setContentType("application/x-json");
		try {response.getWriter().print(jObject);
		} catch (IOException e) {e.printStackTrace();}
		
	}
	
	
	//Ajax request for assign new Phone
	@RequestMapping(value="/assignNewPhone.html",method=RequestMethod.GET)
	public void assignNewPhone(HttpServletRequest request,HttpServletResponse res)
	{
		int pId = ((Participant)request.getSession().getAttribute("queryParticipant")).getParticipant_Id();//get participant from http session
		ParticipantControllerUtil.assignNewPhone(pId, request);

	}
	
	//dhtmlx request to get JSON for assigned Sim
	@RequestMapping(value="/getPartAssignedSim.html", method=RequestMethod.GET)
	public void getParticipantAssignedSim(HttpServletRequest request,HttpServletResponse response)
	{
		//Get Participant from Http Session which is set earlier
		int pId = ((Participant)request.getSession().getAttribute("queryParticipant")).getParticipant_Id();
		JSONObject jObject = ParticipantControllerUtil.getAssignedSim(pId);
		response.setContentType("application/x-json");
		try {response.getWriter().print(jObject);
		} catch (IOException e) {e.printStackTrace();}
		
	}
	
	//Ajax request for assign new Sim
	@RequestMapping(value="/assignNewSim.html",method=RequestMethod.GET)
	public void assignNewSim(HttpServletRequest request,HttpServletResponse res)
	{
		int pId = ((Participant)request.getSession().getAttribute("queryParticipant")).getParticipant_Id();//get participant from http session
		ParticipantControllerUtil.assignNewSim(pId, request);

	}
	
	//dhtmlx request to load Assigned wocket grid
	@RequestMapping(value="/getPartAssignedWocket.html", method=RequestMethod.GET)
	public void getParticipantAssignedWockets(HttpServletRequest request,HttpServletResponse response)
	{
		//Get Participant from Http Session which is set earlier
		int pId = ((Participant)request.getSession().getAttribute("queryParticipant")).getParticipant_Id();
		JSONObject jObject = ParticipantControllerUtil.getAssignedWocket(pId);
		response.setContentType("application/x-json");
		try {response.getWriter().print(jObject);
		} catch (IOException e) {e.printStackTrace();}
		
	}
	
	//Ajax request for assigning new Wockets
	@RequestMapping(value="/assignNewWockets.html",method=RequestMethod.GET)
	public void assignNewWockets(HttpServletRequest request,HttpServletResponse res)
	{
		int pId = ((Participant)request.getSession().getAttribute("queryParticipant")).getParticipant_Id();//get participant from http session
		Session session = HibernateSession.getSession();
		ParticipantControllerUtil.assignWocket(request, session, pId);
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
	}
	
	
	
	
	
	
	
}
