package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.Date;
import java.util.List;

import com.google.gson.annotations.SerializedName;

public class DataUploadEvent {
	
	/**
	 * auto generated in DB
	 */
	private static final int UNDEFINED_INT = -1; 
	
	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	private int dataUploadEventId;
	
	private int participantID;
	 
	@SerializedName("sutime")
	private Date startUploadTime;
	
	@SerializedName("eutime")
	private Date endUploadTime;

	@SerializedName("suc")
	private Boolean resultStatus;
	
	@SerializedName("sdtime")
	private Date startDataTime;
	
	@SerializedName("edtime")
	private Date endDataTime;

	@SerializedName("fname")
	private String fileName;

	@SerializedName("bytes")
	private int fileSize;
	
	@SerializedName("note")
	private String note;
	
	private DataUploadEvent()
	{
		participantID = UNDEFINED_INT;
		startUploadTime = null;
		endUploadTime = null;
		startDataTime = null;
		endDataTime = null;
		fileName = null;
		fileSize = UNDEFINED_INT; 
		note = null; 
	}

	public int getDataUploadEventId() {
		return dataUploadEventId;
	}

	public void setDataUploadEventId(int dataUploadEventId) {
		this.dataUploadEventId = dataUploadEventId;
	}

	public int getParticipantID() {
		return participantID;
	}

	public void setParticipantID(int participantID) {
		this.participantID = participantID;
	}

	public Date getStartUploadTime() {
		return startUploadTime;
	}

	public void setStartUploadTime(Date startUploadTime) {
		this.startUploadTime = startUploadTime;
	}

	public Date getEndUploadTime() {
		return endUploadTime;
	}

	public void setEndUploadTime(Date endUploadTime) {
		this.endUploadTime = endUploadTime;
	}
	

	public Boolean getResultStatus() {
		return resultStatus;
	}

	public void setResultStatus(Boolean resultStatus) {
		this.resultStatus = resultStatus;
	}

	public Date getStartDataTime() {
		return startDataTime;
	}

	public void setStartDataTime(Date startDataTime) {
		this.startDataTime = startDataTime;
	}

	public Date getEndDataTime() {
		return endDataTime;
	}

	public void setEndDataTime(Date endDataTime) {
		this.endDataTime = endDataTime;
	}

	public String getFileName() {
		return fileName;
	}

	public void setFileName(String fileName) {
		this.fileName = fileName;
	}



	public int getFileSize() {
		return fileSize;
	}

	public void setFileSize(int fileSize) {
		this.fileSize = fileSize;
	}

	public String getNote() {
		return note;
	}

	public void setNote(String note) {
		this.note = note;
	}
	
	
	
	
}
