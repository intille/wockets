/***
 * Created By Salim Khan
 * Contains all wockets data log in List form
 */
package edu.mit.media.wockets.DataLogger;

import java.util.ArrayList;
import java.util.List;

import com.google.gson.annotations.SerializedName;

import edu.mit.media.wockets.DataLogger.DataLoggerBean.*;

public class DataContainer {
	@SerializedName("somePhoneData")
	private List<PhoneStats> phoneStatsList;
	
	@SerializedName("somePrompts")
	private List<Prompting> promptingList;
	
	@SerializedName("someSwaps")
	private List<Swapping> swappingList;
	
	@SerializedName("someWocketData")
	private List<WocketStats> wocketStateList;

	@SerializedName("someWocketStatsData")
	private List<WocketInfo> wocketInfoList;

	@SerializedName("someActivityCountData")
	private List<ActivityCountData> activityCountDataList;
	
	@SerializedName("someSensors")
	private List<Sensor> sensorList;
	
	@SerializedName("somePhones")
	private List<Phone> somePhones; 
	
	@SerializedName("someNotes")
	private List<Note> someNotes;
	
	@SerializedName("someFileUploads")
	private List<DataUploadEvent> someRawUploads;
	
	@SerializedName("someHRData")
	private List<HRData> someHRData;
	
	@SerializedName("phoneID")
	private String phoneId;
	
	public String getPhoneId() {
		return phoneId;
	}

	public void setPhoneId(String phoneId) {
		this.phoneId = phoneId;
	}

	private List<SwappedSensor> swappedSensorList;
	
	public DataContainer()
	{
		this.phoneStatsList = new ArrayList<PhoneStats>();
		this.promptingList = new ArrayList<Prompting>();
		this.swappedSensorList = new ArrayList<SwappedSensor>();
		this.swappingList = new ArrayList<Swapping>();
		this.wocketStateList = new ArrayList<WocketStats>();
		this.wocketInfoList = new ArrayList<WocketInfo>();
		this.activityCountDataList = new ArrayList<ActivityCountData>();
		this.sensorList = new ArrayList<Sensor>();
		this.somePhones = new ArrayList<Phone>();
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

	public List<WocketInfo> getWocketInfoList() {
		return wocketInfoList;
	}

	public List<ActivityCountData> getActivityCountDataList() {
		return activityCountDataList;
	}
	
	public List<Phone> getSomePhones() {
		return somePhones;
	}

	public void setSomePhones(List<Phone> somePhones) {
		this.somePhones = somePhones;
	}

	public List<Note> getSomeNotes() {
		return someNotes;
	}

	public void setSomeNotes(List<Note> someNotes) {
		this.someNotes = someNotes;
	}

	public List<DataUploadEvent> getSomeRawUploads() {
		return someRawUploads;
	}

	public void setSomeRawUploads(List<DataUploadEvent> someRawUploads) {
		this.someRawUploads = someRawUploads;
	}

	public List<HRData> getSomeHRData() {
		return someHRData;
	}

	public void setSomeHRData(List<HRData> someHRData) {
		this.someHRData = someHRData;
	}
	
}
