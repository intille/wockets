package jsonModel;

import java.io.Serializable;
import java.util.Date;
import java.util.List;

import com.google.gson.annotations.SerializedName;

public class SwappedSensor implements Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	// The serialized names in this class are short to minimize the length of the json string.
	// We sacrifice some readability but this may improve performance on the phone. 
	
	//@SerializedName("mac_id")
	@SerializedName("mac")
	public String macID;
	
	//@SerializedName("body_location")
	@SerializedName("loc")
	public String bodyLocation;
	
	public SwappedSensor()
	{
		macID = null; 
		bodyLocation = null; 
	}
}
