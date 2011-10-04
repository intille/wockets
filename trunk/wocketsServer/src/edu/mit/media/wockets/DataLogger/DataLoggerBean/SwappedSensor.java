package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.io.Serializable;

public class SwappedSensor implements Serializable{
	private int swappingId;
	private String macId;
	private String sensorPlacement;
	private Swapping swapping;
	
	
	
	public Swapping getSwapping() {
		return swapping;
	}
	public void setSwapping(Swapping swapping) {
		this.swapping = swapping;
	}
	public int getSwappingId() {
		return swappingId;
	}
	public void setSwappingId(int swappingId) {
		this.swappingId = swappingId;
	}
	public String getMacId() {
		return macId;
	}
	public void setMacId(String macId) {
		this.macId = macId;
	}
	public String getSensorPlacement() {
		return sensorPlacement;
	}
	public void setSensorPlacement(String sensorPlacement) {
		this.sensorPlacement = sensorPlacement;
	}
	
	
	

}
