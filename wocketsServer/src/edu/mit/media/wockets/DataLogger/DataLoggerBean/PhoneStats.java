package edu.mit.media.wockets.DataLogger.DataLoggerBean;

public class PhoneStats {
	private int phoneStatsId;
	private int participantId;
	private String createDate;
	private String uploadDate;
	private int phoneBattery;
	private int mainMemo;
	private int sdMemo;
	
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
