/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Controller;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.hibernate.Session;
import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.servlet.ModelAndView;

import edu.mit.media.wockets.Beans.User;
import edu.mit.media.wockets.utility.HibernateSession;
import edu.mit.media.wockets.utility.PasswordEnrypDecryp;

@Controller
public class CommonController {
	@RequestMapping(value="/personalInfo.html", method=RequestMethod.GET)
	public ModelAndView personalInfo(HttpServletRequest req, HttpServletResponse res)
	{
		User user = (User)req.getSession().getAttribute("userObject");
		return new ModelAndView("PersonalINfo","user",user);
	}
	

	@RequestMapping(value="/oldPwdValidation.html", method=RequestMethod.POST)
	public @ResponseBody String oldPwdValidation(HttpServletRequest req)
	{
		String oldPwd = req.getParameter("oldPwd");
		try{oldPwd = PasswordEnrypDecryp.encrypt(oldPwd);}
		catch(Exception ex){ex.printStackTrace();}
		return oldPwd;
	}
	@RequestMapping(value="/updatePersonalInfo.html", method=RequestMethod.POST)
	public ModelAndView updatePersonalInfo(@ModelAttribute("user") User user,HttpServletRequest req)
	{
		Session session = HibernateSession.getSession();
		String changePwd = req.getParameter("changePwd");
		if(changePwd.equals("yes"))
		{
			String newPwd = null;
			try{
				newPwd = PasswordEnrypDecryp.encrypt(req.getParameter("newPwd"));
				}
			catch(Exception e){e.printStackTrace();}
			user.getAccount().setPwd(newPwd);
         }
		session.update(user);
		HibernateSession.sessionClose(session);
		return new ModelAndView("PersonalINfo","user",user);
	}

}
