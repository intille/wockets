package jsonModel;

import java.io.Serializable;
import java.util.Date;
import java.util.List;

import com.google.gson.annotations.SerializedName;

public class HRData implements Serializable{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public static final int UNDEFINED_INT = -1; 

	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	// This value is set on the server and should not be set by the client 
	@SerializedName("pid")
	public int participantID;
		 
	@SerializedName("hid")
	public String hardwareID;
	
	@SerializedName("time")
	public Date createTime;
	
	@SerializedName("hr")
	public int heartRate;

	@SerializedName("hbnum")
	public int heartBeatNumber;
		
	@SerializedName("bat")
	public int battery;
	
	public HRData()
	{
		participantID = UNDEFINED_INT;
		hardwareID = null;
		createTime = null;
		heartRate = UNDEFINED_INT; 
		heartBeatNumber = UNDEFINED_INT;
		battery = UNDEFINED_INT; 
	}
}
