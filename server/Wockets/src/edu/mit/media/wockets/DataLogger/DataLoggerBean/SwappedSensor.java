package edu.mit.media.wockets.DataLogger.DataLoggerBean;

import java.io.Serializable;

import com.google.gson.annotations.SerializedName;

public class SwappedSensor implements Serializable{
	private int swappingId;
	
	@SerializedName("mac")
	private String macId;
	
	@SerializedName("loc")
	private String sensorPlacement;
	
	
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
