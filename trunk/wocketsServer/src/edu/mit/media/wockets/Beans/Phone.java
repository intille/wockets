/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

public class Phone {
private String IMEI;
private String phoneModel;
private String platform;
private String OSVersion;
private String appVersion;
private char isAssigned;
public String getIMEI() {
	return IMEI;
}
public void setIMEI(String iMEI) {
	IMEI = iMEI;
}
public String getPhoneModel() {
	return phoneModel;
}
public void setPhoneModel(String phoneModel) {
	this.phoneModel = phoneModel;
}
public String getPlatform() {
	return platform;
}
public void setPlatform(String platform) {
	this.platform = platform;
}
public String getOSVersion() {
	return OSVersion;
}
public void setOSVersion(String oSVersion) {
	OSVersion = oSVersion;
}
public String getAppVersion() {
	return appVersion;
}
public void setAppVersion(String appVersion) {
	this.appVersion = appVersion;
}
public char getIsAssigned() {
	return isAssigned;
}
public void setIsAssigned(char isAssigned) {
	this.isAssigned = isAssigned;
}


	
}
