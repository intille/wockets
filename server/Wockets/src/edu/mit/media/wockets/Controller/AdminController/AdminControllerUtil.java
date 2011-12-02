package edu.mit.media.wockets.Controller.AdminController;

import java.util.List;

import org.hibernate.Query;
import org.hibernate.Session;

import com.ibm.icu.util.StringTokenizer;

import edu.mit.media.wockets.Beans.StudyReviewCheck;
import edu.mit.media.wockets.Beans.User;
import edu.mit.media.wockets.Beans.UserAssignedStudy;

public class AdminControllerUtil {
	
	//Updating or adding new User Assigned study record for user
	@SuppressWarnings("all")
	public static void assignOrUpdateUserAssgStd(Session session,String userName,String concatIds)
	{
		Query q = session.createQuery("From User where User_Name =:uName");
		q.setString("uName",userName);
		List<User> uList = (List<User>)q.list();
		int uId = uList.get(0).getUser_Id();
		//delete all record if exist in USER_ASSIGNED_STUDY table for user
		q = session.createQuery("Delete FROM UserAssignedStudy uStd WHERE User_ID =:uId");
		q.setInteger("uId",uId);
		q.executeUpdate();
		//entering all record for concat string Id in User_Assigned_study table
		StringTokenizer sTknz = new StringTokenizer(concatIds,"|");
		while(sTknz.hasMoreTokens())
		{
			String studyId = sTknz.nextToken();
			UserAssignedStudy uStudy = new UserAssignedStudy();
			uStudy.setStudyId(studyId);
			uStudy.setUserId(uId);
			session.save(uStudy);
		}

	}
	//add checkList to Table STUDY_REVIEW_CHECKLIST
	public static void assignCheckListToStudy(String selectedReviewCheck,String studyId, Session session)
	{
		String[] checkIds= selectedReviewCheck.split(":");
		for(String id: checkIds)
		{
			StudyReviewCheck studyReviewCheck = new StudyReviewCheck();
			studyReviewCheck.setCheckId(Integer.parseInt(id));
			studyReviewCheck.setStudyId(studyId);
			session.save(studyReviewCheck);
		}
	}
	//update checkList for selected Study
	public static void assignStudyCheckListUpdate(String selectedReviewCheck,String studyId, Session session)
	{
		//delete all record for studyId
		Query q = session.createQuery("DELETE FROM StudyReviewCheck WHERE Study_Id =:studyId");
		q.setString("studyId",studyId);
		q.executeUpdate();
		session.flush();
		session.clear();
		//enter new selected record
		assignCheckListToStudy(selectedReviewCheck,studyId, session);
	}

}
