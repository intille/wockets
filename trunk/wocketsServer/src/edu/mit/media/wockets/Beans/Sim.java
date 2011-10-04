/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

public class Sim {
	private String phoneNbr;
	private String carrier;
	private String contractExpDate;
	private char isAssigned;
	private String notes;
	
	public String getPhoneNbr() {
		return phoneNbr;
	}
	public void setPhoneNbr(String phoneNbr) {
		this.phoneNbr = phoneNbr;
	}
	public String getCarrier() {
		return carrier;
	}
	public void setCarrier(String carrier) {
		this.carrier = carrier;
	}
	public String getContractExpDate() {
		return contractExpDate;
	}
	public void setContractExpDate(String contractExpDate) {
		this.contractExpDate = contractExpDate;
	}
	public char getIsAssigned() {
		return isAssigned;
	}
	public void setIsAssigned(char isAssigned) {
		this.isAssigned = isAssigned;
	}
	public String getNotes() {
		return notes;
	}
	public void setNotes(String notes) {
		this.notes = notes;
	}
	
	

}
