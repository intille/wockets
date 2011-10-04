/*
 * Created By Salim Khan
 * Util for generate default USER_Id and PWD for new User
 */
package edu.mit.media.wockets.utility;

import java.util.Random;

public class NewUserUtil {
	//default user id is user assigned role concat with user last name
	public static String getDefaultPassword(String role, String lName)
	{	
		String pwd = role+lName;
		return pwd;
	}
	//default password is user role and unique generated ID of user
	public static String getDefaultUserName(String role, int userId)
	{
		return role+userId;
	}

}
