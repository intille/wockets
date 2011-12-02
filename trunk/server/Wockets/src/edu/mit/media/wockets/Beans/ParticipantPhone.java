/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

import java.io.Serializable;

public class ParticipantPhone implements Serializable{
	
	private int participantId;
	private String imei;
	private Character activeStatus;
	private String inactiveReason;
	
	
	
	public String getInactiveReason() {
		return inactiveReason;
	}
	public void setInactiveReason(String inactiveReason) {
		this.inactiveReason = inactiveReason;
	}
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
	}
	public String getImei() {
		return imei;
	}
	public void setImei(String imei) {
		this.imei = imei;
	}
	public Character getActiveStatus() {
		return activeStatus;
	}
	public void setActiveStatus(Character activeStatus) {
		this.activeStatus = activeStatus;
	}
	
}
