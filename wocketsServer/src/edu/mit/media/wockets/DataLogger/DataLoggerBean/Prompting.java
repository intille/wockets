package edu.mit.media.wockets.DataLogger.DataLoggerBean;

public class Prompting {
	private int promptId;
	private int participantId;
	private String promptType;
	private String promptTime;
	private String responseTime;
	private int activityInterval;
	private String primaryActivity;
	private String alternateActivity;
	
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
	
	

}
