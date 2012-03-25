//package edu.mit.media.wockets.DataLogger.DataLoggerBean;
//
//import java.util.ArrayList;
//import java.util.Date;
//import java.util.HashSet;
//import java.util.List;
//import java.util.Set;
//
//import com.google.gson.annotations.SerializedName;
//
//public class Swapping {
//	private int swappingId;
//	
//	private int participantId;
//	
//	//*****************for GSON 
//	@SerializedName("swap")
//	private boolean isSwap;
//	@SerializedName("restart")
//	private boolean isRestarted;
//	@SerializedName("locchange")
//	private boolean isLocationChange;
//	@SerializedName("time")
//	private Date dateTime;
//	
//	public boolean isSwap() {
//		return isSwap;
//	}
//	public void setSwap(boolean isSwap) {
//		this.isSwap = isSwap;
//	}
//	public boolean isRestarted() {
//		return isRestarted;
//	}
//	public void setRestarted(boolean isRestarted) {
//		this.isRestarted = isRestarted;
//	}
//	public boolean isLocationChange() {
//		return isLocationChange;
//	}
//	public void setLocationChange(boolean isLocationChange) {
//		this.isLocationChange = isLocationChange;
//	}
//	public Date getDateTime() {
//		return dateTime;
//	}
//	public void setDateTime(Date dateTime) {
//		this.dateTime = dateTime;
//	}
//	
//	///*************************************
//	private String swapEvent;
//	private String restartedEvent;
//	private String loctChangedevent;
//	private String swapTime;
//	private String uploadTime;
//	
//	//private Set<SwappedSensor> swappedSensor = new HashSet<SwappedSensor>(0);
//	@SerializedName("someSwappedSensors")
//	private List<SwappedSensor> swappedSensor = new ArrayList<SwappedSensor>();
//	
//	public List<SwappedSensor> getSwappedSensor() {
//		return swappedSensor;
//	}
//	public void setSwappedSensor(List<SwappedSensor> swappedSensor) {
//		this.swappedSensor = swappedSensor;
//	}
//
////public Set<SwappedSensor> getSwappedSensor() {
////		return swappedSensor;
////	}
////	public void setSwappedSensor(Set<SwappedSensor> swappedSensor) {
////		this.swappedSensor = swappedSensor;
////	}
//
//	public int getSwappingId() {
//		return swappingId;
//	}
//	public void setSwappingId(int swappingId) {
//		this.swappingId = swappingId;
//	}
//	public String getRestartedEvent() {
//		return restartedEvent;
//	}
//	public void setRestartedEvent(String restartedEvent) {
//		this.restartedEvent = restartedEvent;
//	}
//	public int getParticipantId() {
//		return participantId;
//	}
//	public void setParticipantId(int participantId) {
//		this.participantId = participantId;
//	}
//	public String getSwapTime() {
//		return swapTime;
//	}
//	public void setSwapTime(String swapTime) {
//		this.swapTime = swapTime;
//	}
//	public String getUploadTime() {
//		return uploadTime;
//	}
//	public void setUploadTime(String uploadTime) {
//		this.uploadTime = uploadTime;
//	}
//	public String getSwapEvent() {
//		return swapEvent;
//	}
//	public void setSwapEvent(String swapEvent) {
//		this.swapEvent = swapEvent;
//	}
//	public String getLoctChangedevent() {
//		return loctChangedevent;
//	}
//	public void setLoctChangedevent(String loctChangedevent) {
//		this.loctChangedevent = loctChangedevent;
//	}
//}
//


package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.ArrayList;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.gson.annotations.SerializedName;

public class Swapping {

	private int swappingId;
	private int participantId;
		
	//*****************for GSON 
	@SerializedName("swap")
	private boolean isSwap;
	@SerializedName("restart")
	private boolean isRestarted;
	@SerializedName("loc")
	private boolean isLocationChange;
	@SerializedName("sTime")
	private Date swapTime;
	@SerializedName("uTime")
	private Date uploadTime;
	
	public boolean getIsSwap() {
		return isSwap;
	}
	public void setIsSwap(boolean isSwap) {
		this.isSwap = isSwap;
	}
	public boolean getIsRestarted() {
		return isRestarted;
	}
	public void setIsRestarted(boolean isRestarted) {
		this.isRestarted = isRestarted;
	}
	public boolean getIsLocationChange() {
		return isLocationChange;
	}
	public void setIsLocationChange(boolean isLocationChange) {
		this.isLocationChange = isLocationChange;
	}
	public int getSwappingId() {
		return swappingId;
	}
	public void setSwappingId(int swappingId) {
		this.swappingId = swappingId;
	}
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
	}
	public Date getSwapTime() {
		return swapTime;
	}
	public void setSwapTime(Date swapTime) {
		this.swapTime = swapTime;
	}
	public Date getUploadTime() {
		return uploadTime;
	}
	public void setUploadTime(Date uploadTime) {
		this.uploadTime = uploadTime;
	}
	

	//private Set<SwappedSensor> swappedSensor = new HashSet<SwappedSensor>(0);
	@SerializedName("someSwappedSensors")
	private List<SwappedSensor> swappedSensor = new ArrayList<SwappedSensor>();
	
	public List<SwappedSensor> getSwappedSensor() {
		return swappedSensor;
	}
	public void setSwappedSensor(List<SwappedSensor> swappedSensor) {
		this.swappedSensor = swappedSensor;
	}
}
