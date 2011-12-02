/**
 * Created By Salim Khan
 * Reviewer Data check functionality controller
 */
package edu.mit.media.wockets.Controller.ReviewerController;

import java.io.IOException;
import java.util.List;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import net.sf.json.JSONArray;

import org.hibernate.Query;
import org.hibernate.SQLQuery;
import org.hibernate.Session;
import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.servlet.ModelAndView;

import edu.mit.media.wockets.Beans.StudyReviewCheck;
import edu.mit.media.wockets.utility.HibernateSession;

@Controller
public class ReviewerDataCheckController {
	
	//get check list for selected study
	@RequestMapping(value="/getStudyCheckList.html",method=RequestMethod.GET)
	public void getStudyAssignedCheckList(HttpServletRequest req, HttpServletResponse res)
	{
		JSONArray assignedCheck = new JSONArray();
		String studyId =req.getParameter("studyId");
		Session session = HibernateSession.getSession();
		SQLQuery sqlQuery = session.createSQLQuery("SELECT RC.Check_Id, RC.Check_Parameter FROM REVIEWER_CHECKLIST RC " +
				                                   "INNER JOIN STUDY_REVIEW_CHECKLIST SC ON RC.Check_Id = SC.Check_Id" +
				                                   " WHERE SC.Study_Id =:studyId");
		sqlQuery.setString("studyId", studyId);
		List list = sqlQuery.list();
		HibernateSession.sessionClose(session);
		for(int i=0 ; i < list.size(); i++)
		{	
			Object[] objectList = (Object[])list.get(i);
			JSONArray check = new JSONArray();
			check.add(objectList[0]);
			check.add(objectList[1]);
			assignedCheck.add(check);
		}

		res.setContentType("application/x-json");
		try {res.getWriter().print(assignedCheck);
		} catch (IOException e) {e.printStackTrace();}
		
	}
	
	//child Data check Action window Request
	@RequestMapping(value="/DataCheckAction.html", method=RequestMethod.GET)
	public ModelAndView openDataCheckActionWindow(HttpServletRequest req, HttpServletResponse res)
	{
		int pId = Integer.parseInt(req.getParameter("pId"));
		
		return new ModelAndView("DataCheckAction","pId",pId);
	}

}
