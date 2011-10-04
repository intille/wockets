package edu.mit.media.wockets.Controller.AdminController;

import java.util.List;

import org.hibernate.Query;
import org.hibernate.Session;

import com.ibm.icu.util.StringTokenizer;

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

}
