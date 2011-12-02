/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

import java.io.Serializable;

public class UserAssignedStudy implements Serializable {
	private int userId;
	private String studyId;
	
	public int getUserId() {
		return userId;
	}
	public void setUserId(int userId) {
		this.userId = userId;
	}
	public String getStudyId() {
		return studyId;
	}
	public void setStudyId(String studyId) {
		this.studyId = studyId;
	}
	
	

}
