/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

import java.io.Serializable;

public class ParticipantSim implements Serializable{
	private int participantId;
	private String phoneNbr;
	private char activeStatus;
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
	public String getPhoneNbr() {
		return phoneNbr;
	}
	public void setPhoneNbr(String phoneNbr) {
		this.phoneNbr = phoneNbr;
	}
	public char getActiveStatus() {
		return activeStatus;
	}
	public void setActiveStatus(char activeStatus) {
		this.activeStatus = activeStatus;
	}
	
	
	

}
