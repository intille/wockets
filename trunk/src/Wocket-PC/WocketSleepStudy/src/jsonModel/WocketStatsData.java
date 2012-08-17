package jsonModel;

import java.util.Date;
import java.util.List;

import com.google.gson.annotations.SerializedName;

public class WocketStatsData {
	
	public static final int UNDEFINED_INT = -1; 

	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	// This value is set on the server and should not be set by the client 
	@SerializedName("pid")
	public int participantID;
	
	@SerializedName("mac")
	public String macID;
	
	@SerializedName("time")
	public Date createTime;
	
	@SerializedName("bat")
	public int wocketBattery;

	@SerializedName("tbyte")
	public int transmittedBytes;

	@SerializedName("rbyte")
	public int receivedBytes;
	
	public WocketStatsData()
	{
		participantID = UNDEFINED_INT;
		macID = null;
		createTime = null;
		wocketBattery = UNDEFINED_INT;
		transmittedBytes = UNDEFINED_INT;
		receivedBytes = UNDEFINED_INT;		
	}
}
