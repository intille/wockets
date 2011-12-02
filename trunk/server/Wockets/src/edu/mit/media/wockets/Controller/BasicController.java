/*
 * Created By Salim Khan
 * Controller for all user
 */
package edu.mit.media.wockets.Controller;

import java.util.List;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.hibernate.Query;
import org.hibernate.Session;
import org.springframework.context.ApplicationContext;
import org.springframework.context.support.ClassPathXmlApplicationContext;
import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.servlet.ModelAndView;
import edu.mit.media.wockets.Beans.*;



import edu.mit.media.wockets.Beans.Account;
import edu.mit.media.wockets.utility.*;


@Controller
public class BasicController {
	//request for home page
	@RequestMapping("/home.html")
	public ModelAndView homePage()
	{
		return new ModelAndView("home");
	}
	//request for login page
	@RequestMapping("/loginPage.html")
	public ModelAndView loginPage()
	{
		return new ModelAndView("login");
	}
	//login submit request
	@RequestMapping(value="/loginSubmit.html" , method= RequestMethod.POST)
	public ModelAndView login(HttpServletRequest req, HttpServletResponse resp)
	{
		String userName = req.getParameter("userName");
		String pwd = req.getParameter("pwd");
		try{
		pwd = PasswordEnrypDecryp.encrypt(pwd);}//encrypt entered password to match
		catch(Exception e){e.printStackTrace();}
		Session session = edu.mit.media.wockets.utility.HibernateSession.getSession();
		Query q = session.createQuery("From User Users Where User_Name=:userName");//check user name
		q.setString("userName",userName);
		List accList = q.list();
		if(accList.size()==0){
			String err = "Invalid User Name.";
			return (new ModelAndView("login","err",err));
		}
		User user = (User)accList.get(0);
		
		if(!user.getAccount().getPwd().equals(pwd))
		{
			String err = "Invalid Password";
			return (new ModelAndView("login","err",err));
		}

		String role = user.getAccount().getRole();
		String viewName = null;
		if(role.equals("Admin"))
		{
			viewName="adminWorkArea";
			req.getSession().setAttribute("UserRole","A");
		}
		else if (role.equals("Reviewer"))
		{
			viewName = "reviewerWorkArea";
			req.getSession().setAttribute("UserRole","R");
		}

		HibernateSession.sessionClose(session);
		req.getSession().setAttribute("userObject",user);//set user object into http session
		return new ModelAndView(viewName,"role",role);
	
	}

	@RequestMapping(value="/logout.html" , method= RequestMethod.GET)
	public ModelAndView logout(HttpServletRequest req, HttpServletResponse res)
	{
		req.getSession().invalidate();
		return new ModelAndView("home");
	}
	
	//Access denied page
	@RequestMapping(value="/AccessDenied.html")
	public ModelAndView accessdenied()
	{
		return new ModelAndView("AccessDenied");
	}
	
	//Account recovery page
	@RequestMapping(value="/accountRecovery.html")
	public ModelAndView accountRecoveryPage()
	{
		return new ModelAndView("AccountRecovery");
	}
	@RequestMapping(value="/recoverAccount.html",method=RequestMethod.GET)
	public @ResponseBody String recoverAccount(HttpServletRequest req, HttpServletResponse res)
	{
		String result = "true";
		String email = req.getParameter("email");
		Session session = HibernateSession.getSession();
		Query q = session.createQuery("From User Users Where Email=:email");
		q.setString("email",email);
		List<User> list = (List<User>)q.list(); 
		session.flush();
		session.clear();
		HibernateSession.sessionClose(session);
		String message = "Your wockets account details are\n";
		for(User user:list)
		{
			Account acct = user.getAccount();
			message +="Role: "+acct.getRole()+"\n";
			message += "User name: "+acct.getUserName()+"\n";
			String pwd = "";
			try{pwd = PasswordEnrypDecryp.decrypt(acct.getPwd());}
			catch(Exception e){e.printStackTrace();}
			message += "Password: "+pwd+"\n\n\n";
		}
		
		if(list.size()>0)
		{
			ApplicationContext context = new ClassPathXmlApplicationContext("spring-mail.xml");
			Mail mailUtil = (Mail)context.getBean("mail");
			String subject = "Your Wocket Account details.";
			mailUtil.sendMail("User",message,email,subject);
		}
		else
			result = "false";
		return result;
	}

}
