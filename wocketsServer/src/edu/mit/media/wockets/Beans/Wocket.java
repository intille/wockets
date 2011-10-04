/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

public class Wocket {
	private String wocketId;
	private String colorSet;
	private String hardwareVersion;
	private String firmwareVersion;
	private char printed_Id;
	private String notes;
	private char isAssigned;
	
	public String getWocketId() {
		return wocketId;
	}
	public void setWocketId(String wocketId) {
		this.wocketId = wocketId;
	}
	public String getColorSet() {
		return colorSet;
	}
	public void setColorSet(String colorSet) {
		this.colorSet = colorSet;
	}
	public String getHardwareVersion() {
		return hardwareVersion;
	}
	public void setHardwareVersion(String hardwareVersion) {
		this.hardwareVersion = hardwareVersion;
	}
	public String getFirmwareVersion() {
		return firmwareVersion;
	}
	public void setFirmwareVersion(String firmwareVersion) {
		this.firmwareVersion = firmwareVersion;
	}
	public char getPrinted_Id() {
		return printed_Id;
	}
	public void setPrinted_Id(char printed_Id) {
		this.printed_Id = printed_Id;
	}
	public String getNotes() {
		return notes;
	}
	public void setNotes(String notes) {
		this.notes = notes;
	}
	public char getIsAssigned() {
		return isAssigned;
	}
	public void setIsAssigned(char isAssigned) {
		this.isAssigned = isAssigned;
	}
	
	

}
