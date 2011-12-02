/*
 * Created By Salim Khan
 */
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
import org.springframework.web.servlet.ModelAndView;

import edu.mit.media.wockets.Beans.Phone;
import edu.mit.media.wockets.Beans.Sim;
import edu.mit.media.wockets.Beans.Wocket;
import edu.mit.media.wockets.utility.HibernateSession;

@Controller
public class AdminRecordController {
	
	@RequestMapping(value="/phoneDirec.html", method=RequestMethod.GET)
	public ModelAndView phoneDirectory()
	{
		return new ModelAndView("admin-jsp/PhoneDirectory","phone",new Phone());
	}
	
	@RequestMapping(value="/getPhoneDirectory.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getPhoneList(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Phone");
		
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<Phone> phoneList = (List<Phone>)list;
		JSONObject jObj =new JSONObject();
		JSONArray rowListObj=new JSONArray();
		int i = 1;
		for(Phone p: phoneList)
		{	
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);
			JSONArray rowData=new JSONArray();
			rowData.add(p.getIMEI());
			rowData.add(p.getPhoneModel());
			rowData.add(p.getPlatform());
			rowData.add(p.getOSVersion());
			rowData.add(p.getAppVersion());
			if(p.getIsAssigned()=='1')
				rowData.add("Assigned");
			if(p.getIsAssigned()=='0')
				rowData.add("Not Assigned");
			if(p.getIsAssigned()=='2')
				rowData.add("Pending");

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
			i++;
			
		}
		jObj.put("rows",rowListObj);
		res.setContentType("application/x-json");
		try {
			res.getWriter().print(jObj);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	@RequestMapping(value = "/submitPhone.html", method = RequestMethod.GET)
	public ModelAndView submitPhone(@ModelAttribute("phone") Phone phone,BindingResult result,HttpServletRequest req)
	{
		phone.setIsAssigned('0');
		Session session = HibernateSession.getSession();
		int action = Integer.parseInt(req.getParameter("action"));
		switch (action) {
		case 1:
			session.save(phone);
			break;

		case 2:
			session.update(phone);
			break;
		case 3:
			session.delete(phone);
		}
		
		HibernateSession.sessionClose(session);
		return new ModelAndView("admin-jsp/PhoneDirectory","phone",new Phone());
		
	}
	
	@RequestMapping(value="/simDirec.html", method=RequestMethod.GET)
	public ModelAndView simDirectory()
	{
		return new ModelAndView("admin-js/simDirectory","sim",new Sim());
	}
	
	@RequestMapping(value="/getSimcardList.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getSimCardsList(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Sim");
		
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
	
	@RequestMapping(value = "/submitSimcard.html", method = RequestMethod.GET)
	public ModelAndView submitSimcard(@ModelAttribute("sim") Sim sim,BindingResult result,HttpServletRequest req)
	{
		Session session = HibernateSession.getSession();
		int action = Integer.parseInt(req.getParameter("action"));
		switch (action) {
		case 1:
			session.save(sim);
			break;

		case 2:
			session.update(sim);
			break;
		case 3:
			session.delete(sim);
		}
		
		HibernateSession.sessionClose(session);
		return new ModelAndView("admin-js/simDirectory","sim",new Sim());
		
	}
	
	@RequestMapping(value="wocketsDirectory.html",method=RequestMethod.GET)
	public ModelAndView wocketsDirectory()
	{
		return new ModelAndView("admin-jsp/WocketsDirectory","wocket",new Wocket());
	}
	
	@RequestMapping(value="getWocketseDirectory.html",method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getWocketsDirectory(HttpServletRequest req,HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From Wocket");
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
	
	@RequestMapping(value = "/submitWockets.html", method = RequestMethod.GET)
	public ModelAndView submitWocket(@ModelAttribute("wocket") Wocket wocket,HttpServletRequest req)
	{
		Session session = HibernateSession.getSession();
		int action = Integer.parseInt(req.getParameter("action"));
		switch (action) {
		case 1:
			session.save(wocket);
			break;

		case 2:
			session.update(wocket);
			break;
		case 3:
			session.delete(wocket);
		}
		
		HibernateSession.sessionClose(session);
		return new ModelAndView("admin-jsp/WocketsDirectory","wocket",new Wocket());
		
	}
	
	
	

	
	
	

}
