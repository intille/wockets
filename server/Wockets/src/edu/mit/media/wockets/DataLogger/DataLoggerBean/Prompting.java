package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;

import com.google.gson.annotations.SerializedName;

public class Prompting {
	
	/*
	 * Use @SerializedName for GSON
	 *  dateTime comes from JSON need to convert into yyyy-MM-dd HH:mm:ss format then set into createDate
	 */
	private int promptId;
	
	private int participantId;
	
	@SerializedName("type")
	private String promptType;
	
	@SerializedName("int")
	private int activityInterval;
	
	@SerializedName("pact")
	private String primaryActivity;
	
	@SerializedName("aact")
	private String alternateActivity;
	
	@SerializedName("ptime")
	private Date pTime;
	
	@SerializedName("rtime")
	private Date rTime;
	
	public Date getpTime() {
		return pTime;
	}
	public void setpTime(Date pTime) {
		this.pTime = pTime;
	}
	public Date getrTime() {
		return rTime;
	}
	public void setrTime(Date rTime) {
		this.rTime = rTime;
	}

	//**********************************
	
	
	private String promptTime;
	private String responseTime;
	
	public int getPromptId() {
		return promptId;
	}
	public void setPromptId(int promptId) {
		this.promptId = promptId;
	}
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
	}
	public String getPromptType() {
		return promptType;
	}
	public void setPromptType(String promptType) {
		this.promptType = promptType;
	}
	public String getPromptTime() {
		return promptTime;
	}
	public void setPromptTime(String promptTime) {
		this.promptTime = promptTime;
	}
	public String getResponseTime() {
		return responseTime;
	}
	public void setResponseTime(String responseTime) {
		this.responseTime = responseTime;
	}
	public int getActivityInterval() {
		return activityInterval;
	}
	public void setActivityInterval(int activityInterval) {
		this.activityInterval = activityInterval;
	}
	public String getPrimaryActivity() {
		return primaryActivity;
	}
	public void setPrimaryActivity(String primaryActivity) {
		this.primaryActivity = primaryActivity;
	}
	public String getAlternateActivity() {
		return alternateActivity;
	}
	public void setAlternateActivity(String alternateActivity) {
		this.alternateActivity = alternateActivity;
	}
	
	
    @Override
    public boolean equals(Object otherObj)
   {
    	if(otherObj instanceof Prompting)
    	{
    		Prompting pr = (Prompting) otherObj;
    		if(this.participantId==pr.participantId && this.promptType.equals(pr.promptType) && this.promptTime.equals(pr.promptTime)
    			&& this.responseTime.equals(pr.responseTime) && this.activityInterval==pr.activityInterval && this.primaryActivity.equals(pr.primaryActivity)
    			&& this.alternateActivity.equals(pr.alternateActivity))
    			return true;
    		else
    			return false;
    		
    	}
    	else
    		return false;
   }
    
   @Override
   public int hashCode()
   {
	   if(participantId!=0 && promptTime!= null)
		   return (participantId+promptTime).hashCode();
	   else
		   return 127;
   }
	
	

}
