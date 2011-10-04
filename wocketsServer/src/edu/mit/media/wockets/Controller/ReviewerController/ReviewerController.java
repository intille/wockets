/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Controller.ReviewerController;

import java.io.IOException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import net.sf.json.JSONObject;

import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.servlet.ModelAndView;
import edu.mit.media.wockets.Beans.User;


@Controller
public class ReviewerController {
	
	//return User assigned study page
	@RequestMapping(value="reviewerAssignedStudy.html", method=RequestMethod.GET)
	public ModelAndView assignedStudyForm()
	{
		return new ModelAndView("reviewer-jsp/AssignedStudy");
	}
	
	//dhtmlx load request for assigned study list for user
	@RequestMapping(value="reviewerGetAssignedStudy.html", method=RequestMethod.GET)
	@SuppressWarnings("all")
	public void getAssignedStudy(HttpServletRequest request, HttpServletResponse response)
	{
		int userId = ((User)(request.getSession().getAttribute("userObject"))).getUser_Id();
		JSONObject jObj = ReviewerControllerUtil.getUserAssignedStudy(userId);
		response.setContentType("application/x-json");
		try {response.getWriter().print(jObj);}
		catch (IOException e) {e.printStackTrace();}
	}
	
	
	//*******************Review Page**************************//
	@RequestMapping(value="reviewerReviewPage.html",method=RequestMethod.GET)
	public ModelAndView reviewPage()
	{
		return new ModelAndView("reviewer-jsp/ReviewPage");
	}
	
	//dhtmlx request to get study Participants
	@RequestMapping(value="reviewerGetStudyParticipants.html",method=RequestMethod.GET)
	public void getStudyParticipant(HttpServletRequest request, HttpServletResponse response)
	{
		String studyId = request.getParameter("studyId");
		JSONObject jObj = ReviewerControllerUtil.getStudyParticipantList(studyId);
		response.setContentType("application/x-json");
		try {response.getWriter().print(jObj);}
		catch (IOException e) {e.printStackTrace();}
	}
	
	//Ajax request to get participant data for selected date
	@RequestMapping(value="getParticipantChartData.html",method=RequestMethod.POST)
	public void getPartChartData(HttpServletRequest req,HttpServletResponse res)
	{
		int pId = Integer.parseInt(req.getParameter("pId"));
		String date = req.getParameter("date");
		JSONObject chartData = ReviewerControllerUtil.getchartData(pId,date);
		res.setContentType("application/x-json");
		try {res.getWriter().print(chartData);}
		catch (IOException e) {e.printStackTrace();}
	}
	
	//Review Admin configuration page
	@RequestMapping(value="/reviewerConfig.html",method=RequestMethod.GET)
	public ModelAndView configPage()
	{
		return new ModelAndView("reviewerConfig");
	}
	
	
	

}
