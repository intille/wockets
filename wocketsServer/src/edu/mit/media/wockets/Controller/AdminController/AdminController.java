package edu.mit.media.wockets.Controller.AdminController;

import java.io.IOException;
import java.util.List;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import net.sf.json.JSONArray;
import net.sf.json.JSONObject;

import org.hibernate.Query;
import org.hibernate.SQLQuery;
import org.hibernate.Session;
import org.springframework.context.ApplicationContext;
import org.springframework.context.support.ClassPathXmlApplicationContext;
import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.servlet.ModelAndView;

import edu.mit.media.wockets.Beans.*;
import edu.mit.media.wockets.utility.*;

@Controller
public class AdminController {
	
	private Mail mailUtil;
	
	@RequestMapping(value="/studyDirectory.html", method=RequestMethod.GET)
	public ModelAndView studyDirectory()
	{
		return new ModelAndView("StudyDirectory");
	}
	
	//Getting all Study List by dhtmlx request
	@RequestMapping(value="/getStudyList.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getStudyList(HttpServletRequest req, HttpServletResponse res)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From StudyType");
		
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<StudyType> studyList = (List<StudyType>)list;
		JSONObject jObj =new JSONObject();
		JSONArray rowListObj=new JSONArray();
		int i = 1;
		for(StudyType s: studyList)
		{	
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);
			JSONArray rowData=new JSONArray();
			rowData.add(s.getStudy_Id());
			rowData.add(s.getDesc());
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
	
	//add, delete or update study depend on actionType parameter
	@RequestMapping(value="/submitStudy.html" ,method=RequestMethod.GET)
	public @ResponseBody String submitStudy(HttpServletRequest req, HttpServletResponse res)
	{
		StudyType newStudy = new StudyType();
		newStudy.setStudy_Id(req.getParameter("studyId"));
		newStudy.setDesc(req.getParameter("desc"));
		Session session = HibernateSession.getSession();
		int actionType = Integer.parseInt(req.getParameter("actionType"));
		String result = "true";
		/********1 is for Add new Study********
		********2 is for update study**********
		*******3 is for delete study**********/
		switch (actionType) {
		case 1:
			try{session.save(newStudy);}
			catch(Exception e){result = "false";}
			break;

		case 2:
			session.update(newStudy);
			break;
		case 3:
			session.delete(newStudy);
		}
		try{HibernateSession.sessionClose(session);}
		catch(Exception e){result = "false";}
		return result;
	}
	

	/*******************************************************
	 * ********************User Account Management*********
	 * ****************************************************
	 */
	
	@RequestMapping(value="/userAccountDirec.html" ,method=RequestMethod.GET)
	public ModelAndView userAccountDirectory()
	{
		
		return new ModelAndView("UserAccountDirectory");
	}
	
	@RequestMapping(value="/getUserAccountDirectory.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getUserAccountDirectory(HttpServletRequest request, HttpServletResponse response)
	{
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From User");
		
		List list = q.list();
		HibernateSession.sessionClose(session);
		List<User> userList = (List<User>)list;
		JSONObject jObj =new JSONObject();
		JSONArray rowListObj=new JSONArray();
		int i = 1;
		for(User user: userList)
		{
			JSONObject rowObj =new JSONObject();
			rowObj.put("id",i);
			JSONArray rowData=new JSONArray();
			rowData.add(user.getUser_Id());
			rowData.add(user.getfName());
			rowData.add(user.getlName());
			rowData.add(user.getEmail());
			rowData.add(user.getRegist_Date());
			rowData.add(user.getAccount().getRole());
			rowData.add(user.getAccount().getUserName());
			if(user.getActiveStatus()=='1')
				rowData.add("Active");
			else
				rowData.add("In-Active");
			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
			i++;
		}
		jObj.put("rows",rowListObj);
		response.setContentType("application/x-json");
		try {response.getWriter().print(jObj);}
		catch (IOException e) {e.printStackTrace();}
	}
	
	@RequestMapping(value="submitUser.html", method=RequestMethod.GET)
	public void submitUser(HttpServletRequest req, HttpServletResponse res)
	{
		String userName = req.getParameter("userName");
		String fName = req.getParameter("fName");
		String lName = req.getParameter("lName");
		String email = req.getParameter("email");
		char activeStatus= ' ';
		
		if(req.getParameter("activeStatus").equals("De-Activate"))
			activeStatus = '0';
		else
			activeStatus = '1';
		String role = req.getParameter("role");
		int action = Integer.parseInt(req.getParameter("action"));
		Session session = HibernateSession.getSession();
		/********1 is for Add ********
		********2 is for update **********
		*******3 is for delete **********/
		Query q = null;
		switch (action) {
		case 1:
			User user = new User();
			user.setfName(fName);
			user.setlName(lName);
			user.setEmail(email);
			user.setActiveStatus(activeStatus);
			//set account to null for save user personal detail first to get user_Id
			user.setAccount(null);
			session.save(user);
			Account account = new Account();
			user.setAccount(account);

			user.getAccount().setRole(role);
			String pwd = NewUserUtil.getDefaultPassword(role,lName);
			String userId = NewUserUtil.getDefaultUserName(role,user.getUser_Id());

			//************************Send Email to new User************
			ApplicationContext context = new ClassPathXmlApplicationContext("spring-mail.xml");
			mailUtil = (Mail)context.getBean("mail");
			String emailBody = "Your new Wockets account has been created.\nAccount Detail:\nUser Type: "+role+"\nUser Name: "+userId+"\nPassword: "+pwd;
			String subject = "New Wockets Account.";
			mailUtil.sendMail(fName,emailBody,email,subject);

   			try{pwd = PasswordEnrypDecryp.encrypt(pwd);}catch(Exception e){e.printStackTrace();}
			user.getAccount().setPwd(pwd);
			user.getAccount().setUserName(userId);
			//session.save(user);
			session.update(user);
			userName = user.getAccount().getUserName();
			break;

		case 2:
			q = session.createQuery("update User set First_Name=:fName, Last_Name=:lName, Email=:email, Active_Status=:activeStatus where User_Name=:userName");
			q.setString("fName", fName);
			q.setString("lName",lName);
			q.setString("email",email);
			q.setCharacter("activeStatus", activeStatus);
			q.setString("userName",userName);
			q.executeUpdate();
			q = session.createQuery("update Account set Role=:role where User_Name=:userName");
			q.setString("role",role);
			q.setString("userName",userName);
			q.executeUpdate();
			break;
		case 3:
			q = session.createQuery("Delete From Account USER_ACCOUNT Where User_Name =:userName");
			q.setString("userName",userName);
			q.executeUpdate();
			q = session.createQuery("Delete From User USERS Where User_Name =:userName");
			q.setString("userName",userName);
			q.executeUpdate();
			
		}
		
		//Assign or updating User assigned study
		String concatStdId = req.getParameter("concatStdId");
		if(concatStdId !=null)
		{
			AdminControllerUtil.assignOrUpdateUserAssgStd(session, userName, concatStdId);
		}
		
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
		
	}
	
	//Dhtmlx load request for assigned user study list
	@RequestMapping(value="getUserAssignedStudy.html",method=RequestMethod.GET)
	public void getUserAssignedStudy(HttpServletRequest req,HttpServletResponse res)
	{
		int uId = Integer.parseInt(req.getParameter("uId"));
		Session session = HibernateSession.getSession();
		SQLQuery q = session.createSQLQuery("SELECT Study_type.* from Study_Type " +
				                             "INNER JOIN User_Assigned_Study ON Study_Type.Study_Id = User_Assigned_Study.Study_Id " +
				                             "WHERE User_Assigned_Study.User_Id=:uId");
		q.setInteger("uId",uId);
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

			rowObj.put("data",rowData);
			rowListObj.add(rowObj);
         }
		jObj.put("rows",rowListObj);
		res.setContentType("application/x-json");
		try {res.getWriter().print(jObj);
		} catch (IOException e) {e.printStackTrace();}
	}
}
