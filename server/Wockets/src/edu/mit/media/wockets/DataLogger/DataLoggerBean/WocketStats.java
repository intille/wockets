package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;

import com.google.gson.annotations.SerializedName;


// JPN: NOTE!!! 20120311 This class is deprecated. It is left here for backward compatibility. 
// This should be removed in the not-too-distant future.

public class WocketStats {

	public static final int UNDEFINED_INT = -1;
	
	private int wocketStatsId;
	private int participantId = UNDEFINED_INT;

	private String createDate;
	private String uploadDate;
	
	@SerializedName("mac")
	private String macId;
	
	@SerializedName("ac")
	private int activityCount;
	
	@SerializedName("bat")
	private int wocketBattery = UNDEFINED_INT;
	
	@SerializedName("tbyte")
	private int transmittedByte = UNDEFINED_INT;
	
	@SerializedName("rbyte")
	private int receivedBytes = UNDEFINED_INT;
	
	@SerializedName("time")
	private Date dateTime = new Date();
	
	public Date getDateTime() {
		return dateTime;
	}
	public void setDateTime(Date dateTime) {
		this.dateTime = dateTime;
	}
	
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
