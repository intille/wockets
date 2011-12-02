package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;


import com.google.gson.annotations.SerializedName;

public class Note {
	
	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	private int noteId;
	
	@SerializedName("pid")
	private int participantID;
	
	@SerializedName("stime")
	private Date startTime;
	
	@SerializedName("etime")
	private Date endTime;

	@SerializedName("note")
	private String note;
	
	private Note()
	{
		participantID = -1;  //UNDEFINED_INT 
		startTime = null;
		endTime = null;
		note = null; 
	}

	public int getNoteId() {
		return noteId;
	}

	public void setNoteId(int noteId) {
		this.noteId = noteId;
	}

	public int getParticipantID() {
		return participantID;
	}

	public void setParticipantID(int participantID) {
		this.participantID = participantID;
	}

	public Date getStartTime() {
		return startTime;
	}

	public void setStartTime(Date startTime) {
		this.startTime = startTime;
	}

	public Date getEndTime() {
		return endTime;
	}

	public void setEndTime(Date endTime) {
		this.endTime = endTime;
	}

	public String getNote() {
		return note;
	}

	public void setNote(String note) {
		this.note = note;
	}
	
	
}
