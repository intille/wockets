/*
 * Created By Salim Khan
 * All request first handle by this Interceptor
 * checks each url for valid user Role
 * if it not matched then redirect to AccessDenied page  
 */
package edu.mit.media.wockets.interceptor;

import java.util.ArrayList;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;

import org.springframework.web.servlet.handler.HandlerInterceptorAdapter;

public class RoleValidationInterceptor extends HandlerInterceptorAdapter {
	
	private ArrayList<String> adminUrlList = new ArrayList<String>();//admin assigned URL list
	private  ArrayList<String> reviewerUrlList = new ArrayList<String>();//reviewer assigned URL list
	//initialize block runs at object creation time and initialize all list by their URL
	{
		//Admin URL list
		adminUrlList.add("/Wockets/studyDirectory.html");
		adminUrlList.add("/Wockets/getStudyList.html");
		adminUrlList.add("/Wockets/submitStudy.html");
		adminUrlList.add("/Wockets/userAccountDirec.html");
		adminUrlList.add("/Wockets/getUserAccountDirectory.html");
		adminUrlList.add("/Wockets/submitUser.html");
		adminUrlList.add("/Wockets/getUserAssignedStudy.html");
		adminUrlList.add("/Wockets/participantDirectory.html");
		adminUrlList.add("/Wockets/getParticipantDirectory.html");
		adminUrlList.add("/Wockets/getAvailPhoneDirectory.html");
		adminUrlList.add("/Wockets/getAvailableSimcardList.html");
		adminUrlList.add("/Wockets/getAvailableWocketList.html");
		adminUrlList.add("/Wockets/newParticipant.html");
		adminUrlList.add("/Wockets/registerNewParticipant.html");
		adminUrlList.add("/Wockets/manageParticipant.html");
		adminUrlList.add("/Wockets/updatePartPersonalInfo.html");
		adminUrlList.add("/Wockets/getPartAssignedPhone.html");
		adminUrlList.add("/Wockets/assignNewPhone.html");
		adminUrlList.add("/Wockets/getPartAssignedSim.html");
		adminUrlList.add("/Wockets/assignNewSim.html");
		adminUrlList.add("/Wockets/getPartAssignedWocket.html");
		adminUrlList.add("/Wockets/assignNewWockets.html");
		adminUrlList.add("/Wockets/phoneDirec.html");
		adminUrlList.add("/Wockets/getPhoneDirectory.html");
		adminUrlList.add("/Wockets/submitPhone.html");
		adminUrlList.add("/Wockets/simDirec.html");
		adminUrlList.add("/Wockets/getSimcardList.html");
		adminUrlList.add("/Wockets/submitSimcard.html");
		adminUrlList.add("/Wockets/getWocketseDirectory.html");
		adminUrlList.add("/Wockets/wocketsDirectory.html");
		adminUrlList.add("/Wockets/submitWockets.html");
		
		//reviewer URl
		reviewerUrlList.add("/Wockets/reviewerAssignedStudy.html");
		reviewerUrlList.add("/Wockets/reviewerGetAssignedStudy.html");
		reviewerUrlList.add("/Wockets/reviewerReviewPage.html");
		reviewerUrlList.add("/Wockets/reviewerGetStudyParticipants.html");
		reviewerUrlList.add("/Wockets/getParticipantChartData.html");
		reviewerUrlList.add("/Wockets/reviewerDataCheck.html");
		reviewerUrlList.add("/Wockets/getStudyCheckList.html");

	}
	
	/*
	 * PreHandle override method to handle all request before it reaches to actuall mapping controller(non-Javadoc)
	 * @see org.springframework.web.servlet.handler.HandlerInterceptorAdapter#preHandle(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse, java.lang.Object)
	 */
	@Override
	public boolean preHandle(HttpServletRequest request, HttpServletResponse response, Object handler) throws Exception 
	{
	
		String requestUrl = request.getRequestURI();//get request url
		String redirectUrl = "";
		boolean result= true;
		HttpSession httpSession = request.getSession();
		//check USER Role and USer object set in HttpSession at loging time by UserRole and userObject name
		if(adminUrlList.contains(requestUrl))
		{
			if(httpSession.getAttribute("UserRole")==null || !httpSession.getAttribute("UserRole").toString().equals("A")|| httpSession.getAttribute("userObject")==null)
			{
				result = false;
				redirectUrl = "AccessDenied.html";
				response.sendRedirect(redirectUrl);
			}
		}
		else if(reviewerUrlList.contains(requestUrl))
		{
			if(request.getSession().getAttribute("UserRole")==null || !request.getSession().getAttribute("UserRole").toString().equals("R") || httpSession.getAttribute("userObject")==null)
			{
				result = false;
				redirectUrl = "AccessDenied.html";
				response.sendRedirect(redirectUrl);
			}
		}

		return true;
	}

	}
