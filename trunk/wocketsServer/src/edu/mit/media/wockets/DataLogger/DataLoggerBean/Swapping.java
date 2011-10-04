package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.util.HashSet;
import java.util.Set;

public class Swapping {
	private int swappingId;
	private int participantId;
	private String swapTime;
	private String uploadTime;
	private String swapEvent;
	private String restartedEvent;
	private String loctChangedevent;
	
	private Set<SwappedSensor> swappedSensor = new HashSet<SwappedSensor>(0);
	
	
	
public Set<SwappedSensor> getSwappedSensor() {
		return swappedSensor;
	}
	public void setSwappedSensor(Set<SwappedSensor> swappedSensor) {
		this.swappedSensor = swappedSensor;
	}
	//	public SwappedSensor getSwappedSensor() {
//		return swappedSensor;
//	}
//	public void setSwappedSensor(SwappedSensor swappedSensor) {
//		this.swappedSensor = swappedSensor;
//	}
	public int getSwappingId() {
		return swappingId;
	}
	public void setSwappingId(int swappingId) {
		this.swappingId = swappingId;
	}
	public String getRestartedEvent() {
		return restartedEvent;
	}
	public void setRestartedEvent(String restartedEvent) {
		this.restartedEvent = restartedEvent;
	}
	public int getParticipantId() {
		return participantId;
	}
	public void setParticipantId(int participantId) {
		this.participantId = participantId;
	}
	public String getSwapTime() {
		return swapTime;
	}
	public void setSwapTime(String swapTime) {
		this.swapTime = swapTime;
	}
	public String getUploadTime() {
		return uploadTime;
	}
	public void setUploadTime(String uploadTime) {
		this.uploadTime = uploadTime;
	}
	public String getSwapEvent() {
		return swapEvent;
	}
	public void setSwapEvent(String swapEvent) {
		this.swapEvent = swapEvent;
	}

	public String getLoctChangedevent() {
		return loctChangedevent;
	}
	public void setLoctChangedevent(String loctChangedevent) {
		this.loctChangedevent = loctChangedevent;
	}
	
	

}
