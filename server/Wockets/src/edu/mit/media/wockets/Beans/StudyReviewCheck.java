package edu.mit.media.wockets.Beans;

import java.io.Serializable;

public class StudyReviewCheck implements Serializable{
	private String studyId;
	private int checkId;
	
	public String getStudyId() {
		return studyId;
	}
	public void setStudyId(String studyId) {
		this.studyId = studyId;
	}
	public int getCheckId() {
		return checkId;
	}
	public void setCheckId(int checkId) {
		this.checkId = checkId;
	}
	
	

}
