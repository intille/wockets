package jsonModel;

import java.util.Date;
import java.util.List;

import com.google.gson.annotations.SerializedName;

public class PromptEvent {
	
	public static final int UNDEFINED_INT = -1; 

	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 

	// This value is set on the server and should not be set by the client 
	@SerializedName("pid")
	public int participantID;

	@SerializedName("type")
	public String promptType;
	
	@SerializedName("ptime")
	public Date promptTime;

	@SerializedName("rtime")
	public Date responseTime;
	
	@SerializedName("int")
	public int activityInterval;
	
	@SerializedName("pact")
	public String primaryActivity;

	@SerializedName("aact")
	public String alternateActivity;

	public PromptEvent()
	{
		participantID = UNDEFINED_INT;
		promptType = null; 
		promptTime = null;
		responseTime = null;
		activityInterval = UNDEFINED_INT;
		primaryActivity = null;
		alternateActivity = null; 		
	}
	
}
