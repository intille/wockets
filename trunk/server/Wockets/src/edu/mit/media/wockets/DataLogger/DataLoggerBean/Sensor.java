package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.List;

import com.google.gson.annotations.SerializedName;

public class Sensor {
	
	public static final int UNDEFINED_INT = -1; 
	public static final String UNDEFINED_STRING = ""; 

	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 

	//@SerializedName("mac_id")
	@SerializedName("mac")
	public String macID;
	
	//@SerializedName("color")
	@SerializedName("col")
	public String color;
	
	//@SerializedName("hardware_version")
	@SerializedName("hver")
	public double hardwareVersion;
	
	//@SerializedName("firmware_version")
	@SerializedName("fver")
	public double firmwareVersion;
	
	public Sensor()
	{
		macID = UNDEFINED_STRING;
		color = UNDEFINED_STRING; 
		hardwareVersion = 0.0;
		firmwareVersion = 0.0; 
	}	
}
