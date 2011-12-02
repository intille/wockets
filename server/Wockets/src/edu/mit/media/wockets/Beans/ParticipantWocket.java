/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

import java.io.Serializable;

public class ParticipantWocket implements Serializable{
	private int participantId;
	private String wocketId;
	
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
	}
	public String getWocketId() {
		return wocketId;
	}
	public void setWocketId(String wocketId) {
		this.wocketId = wocketId;
	}
	
	

}
