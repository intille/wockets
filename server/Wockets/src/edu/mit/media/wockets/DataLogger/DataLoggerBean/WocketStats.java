package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;

import com.google.gson.annotations.SerializedName;

public class WocketStats {
	private int wocketStatsId;
	
	@SerializedName("pid")
	private int participantId;
	
	@SerializedName("mac")
	private String macId;
	
	@SerializedName("ac")
	private int activityCount;
	
	@SerializedName("bat")
	private int wocketBattery;
	
	@SerializedName("tbyte")
	private int transmittedByte;
	
	@SerializedName("rbyte")
	private int receivedBytes;
	
	@SerializedName("time")
	private Date dateTime;
	
	public Date getDateTime() {
		return dateTime;
	}
	public void setDateTime(Date dateTime) {
		this.dateTime = dateTime;
	}
	
	
	private String createDate;
	private String uploadDate;
	
	public int getWocketStatsId() {
		return wocketStatsId;
	}
	public void setWocketStatsId(int wocketStatsId) {
		this.wocketStatsId = wocketStatsId;
	}
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
	}
	public String getMacId() {
		return macId;
	}
	public void setMacId(String macId) {
		this.macId = macId;
	}
	public String getCreateDate() {
		return createDate;
	}
	public void setCreateDate(String createDate) {
		this.createDate = createDate;
	}
	public String getUploadDate() {
		return uploadDate;
	}
	public void setUploadDate(String uploadDate) {
		this.uploadDate = uploadDate;
	}
	public int getActivityCount() {
		return activityCount;
	}
	public void setActivityCount(int activityCount) {
		this.activityCount = activityCount;
	}
	public int getWocketBattery() {
		return wocketBattery;
	}
	public void setWocketBattery(int wocketBattery) {
		this.wocketBattery = wocketBattery;
	}
	public int getTransmittedByte() {
		return transmittedByte;
	}
	public void setTransmittedByte(int transmittedByte) {
		this.transmittedByte = transmittedByte;
	}
	public int getReceivedBytes() {
		return receivedBytes;
	}
	public void setReceivedBytes(int receivedBytes) {
		this.receivedBytes = receivedBytes;
	}
	
	
	

}
