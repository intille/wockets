package edu.mit.media.wockets.DataLogger.DataLoggerBean;


import com.google.gson.annotations.SerializedName;

public class Phone {
	
	public static final int UNDEFINED_INT = -1; 
	
	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 

	// What else should be in here? 
	
	@SerializedName("pid")
	public int participantID;
	
	@SerializedName("phoneid")
	public String phoneID;
	
	@SerializedName("carrier")
	public String phoneCarrier;

	public Phone()
	{
		participantID = UNDEFINED_INT;
		phoneID = null;
		phoneCarrier = null; 
	}
}
