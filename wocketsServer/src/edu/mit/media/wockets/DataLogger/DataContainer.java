/***
 * Created By Salim Khan
 * Contains all wockets data log in List form
 */
package edu.mit.media.wockets.DataLogger;

import java.util.ArrayList;
import java.util.List;

import edu.mit.media.wockets.DataLogger.DataLoggerBean.*;

public class DataContainer {
	private List<PhoneStats> phoneStatsList;
	private List<Prompting> promptingList;
	private List<SwappedSensor> swappedSensorList;
	private List<Swapping> swappingList;
	private List<WocketStats> wocketStateList;
	
	public DataContainer()
	{
		this.phoneStatsList = new ArrayList<PhoneStats>();
		this.promptingList = new ArrayList<Prompting>();
		this.swappedSensorList = new ArrayList<SwappedSensor>();
		this.swappingList = new ArrayList<Swapping>();
		this.wocketStateList = new ArrayList<WocketStats>();
	}

	public List<PhoneStats> getPhoneStatsList() {
		return phoneStatsList;
	}

	public List<Prompting> getPromptingList() {
		return promptingList;
	}

	public List<SwappedSensor> getSwappedSensorList() {
		return swappedSensorList;
	}

	public List<Swapping> getSwappingList() {
		return swappingList;
	}

	public List<WocketStats> getWocketStateList() {
		return wocketStateList;
	}
	
	
	

}
