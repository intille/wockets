/*
 * Created By Salim Khan
 * Participant Bean for Participant object
 */
package edu.mit.media.wockets.Beans;

public class Participant {
	private int participant_Id;
	private String fName;
	private String lName;
	private char gender;
	private String birth_Date;
	private String email;
	private float height;
	private float weight;
	private String race;
	private char activeStatus;
	private int utc_offset;
	private String notes;
	
	public int getParticipant_Id() {
		return participant_Id;
	}
	public void setParticipant_Id(int participant_Id) {
		this.participant_Id = participant_Id;
	}
	public String getfName() {
		return fName;
	}
	public void setfName(String fName) {
		this.fName = fName;
	}
	public String getlName() {
		return lName;
	}
	public void setlName(String lName) {
		this.lName = lName;
	}
	public char getGender() {
		return gender;
	}
	public void setGender(char gender) {
		this.gender = gender;
	}
	public String getBirth_Date() {
		return birth_Date;
	}
	public void setBirth_Date(String birth_Date) {
		this.birth_Date = birth_Date;
	}
	public String getEmail() {
		return email;
	}
	public void setEmail(String email) {
		this.email = email;
	}
	public float getHeight() {
		return height;
	}
	public void setHeight(float height) {
		this.height = height;
	}
	public float getWeight() {
		return weight;
	}
	public void setWeight(float weight) {
		this.weight = weight;
	}
	public String getRace() {
		return race;
	}
	public void setRace(String race) {
		this.race = race;
	}
	public char getActiveStatus() {
		return activeStatus;
	}
	public void setActiveStatus(char activeStatus) {
		this.activeStatus = activeStatus;
	}
	public int getUtc_offset() {
		return utc_offset;
	}
	public void setUtc_offset(int utc_offset) {
		this.utc_offset = utc_offset;
	}
	public String getNotes() {
		return notes;
	}
	public void setNotes(String notes) {
		this.notes = notes;
	}
	
	
}
