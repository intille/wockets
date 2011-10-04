package edu.mit.media.wockets.DataLogger.DataLoggerBean;

public class WocketStats {
	private int wocketStatsId;
	private int participantId;
	private String macId;
	private String createDate;
	private String uploadDate;
	private int activityCount;
	private int wocketBattery;
	private int transmittedByte;
	private int receivedBytes;
	
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
