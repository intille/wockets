package jsonModel;

import java.util.Date;
import java.util.List;

import com.google.gson.annotations.SerializedName;

public class FileUploadEvent {
	
	public static final int UNDEFINED_INT = -1; 
	
	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	// This value is set on the server and should not be set by the client 
	@SerializedName("pid")
	public int participantID;

	@SerializedName("sutime")
	public Date startUploadTime;
	
	@SerializedName("eutime")
	public Date endUploadTime;

	@SerializedName("suc")
	public boolean isSuccessful;
	
	@SerializedName("sdtime")
	public Date startDataTime;
	
	@SerializedName("edtime")
	public Date endDataTime;

	@SerializedName("fname")
	public String fileName;

	@SerializedName("bytes")
	public int bytes;
	
	@SerializedName("note")
	public String note;
	
	public FileUploadEvent()
	{
		participantID = UNDEFINED_INT;
		startUploadTime = null;
		endUploadTime = null;
		startDataTime = null;
		endDataTime = null;
		fileName = null;
		bytes = UNDEFINED_INT; 
		note = null; 
	}
}
