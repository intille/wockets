package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;

import com.google.gson.annotations.SerializedName;

public class HRData {
	
	private static final int UNDEFINED_INT = -1; 

	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	private int hrDataId;
	
	@SerializedName("pid")
	private int participantID;
	
	@SerializedName("time")
	private Date createTime;
	
	@SerializedName("hr")
	private int heartRate;

	@SerializedName("bat")
	private int battery;
	
	private HRData()
	{
		participantID = UNDEFINED_INT;
		createTime = null;
		heartRate = UNDEFINED_INT; 
		battery = UNDEFINED_INT; 
	}

	
	
	
	public int getHrDataId() {
		return hrDataId;
	}

	public void setHrDataId(int hrDataId) {
		this.hrDataId = hrDataId;
	}

	public int getParticipantID() {
		return participantID;
	}

	public void setParticipantID(int participantID) {
		this.participantID = participantID;
	}

	public Date getCreateTime() {
		return createTime;
	}

	public void setCreateTime(Date createTime) {
		this.createTime = createTime;
	}

	public int getHeartRate() {
		return heartRate;
	}

	public void setHeartRate(int heartRate) {
		this.heartRate = heartRate;
	}

	public int getBattery() {
		return battery;
	}

	public void setBattery(int battery) {
		this.battery = battery;
	}
	
	
	

}
