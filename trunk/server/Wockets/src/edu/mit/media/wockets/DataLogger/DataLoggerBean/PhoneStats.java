package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;

import com.google.gson.annotations.SerializedName;


public class PhoneStats {
	
	/*
	 * Use @SerializedName for GSON
	 *  DateTime comes from JSON need to convert into yyyy-MM-dd HH:mm:ss format then set into createDate
	 */
	private int phoneStatsId;
	
	@SerializedName("pid")
	private int participantId;
		
	@SerializedName("bat")
	private int phoneBattery;
	
	@SerializedName("mem")
	private int mainMemo;
	
	@SerializedName("sdmem")
	private int sdMemo;
	
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
	
	
	public int getPhoneStatsId() {
		return phoneStatsId;
	}
	public void setPhoneStatsId(int phoneStatsId) {
		this.phoneStatsId = phoneStatsId;
	}
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
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
	public int getPhoneBattery() {
		return phoneBattery;
	}
	public void setPhoneBattery(int phoneBattery) {
		this.phoneBattery = phoneBattery;
	}
	public int getMainMemo() {
		return mainMemo;
	}
	public void setMainMemo(int mainMemo) {
		this.mainMemo = mainMemo;
	}
	public int getSdMemo() {
		return sdMemo;
	}
	public void setSdMemo(int sdMemo) {
		this.sdMemo = sdMemo;
	}
	

}
