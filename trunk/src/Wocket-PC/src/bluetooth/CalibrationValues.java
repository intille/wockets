package bluetooth;

import java.util.ArrayList;

/**
 *
 * @author Aida
 */
public class CalibrationValues {
    private String sensorID;    
    private AxesCalibration[] axisCalibration;
    private int samplingRate;
    private int[] battery_calibration;

    public String getSensorID() {
        return sensorID;
    }

    public void setSensorID(String sensorID) {
        this.sensorID = sensorID;
    }   
    
    public CalibrationValues() {
        axisCalibration = new AxesCalibration[] { new AxesCalibration(), new AxesCalibration(), new AxesCalibration() };
        battery_calibration = new int[6];
    }

    public AxesCalibration[] getAxisCalibration() {
        return axisCalibration;
    }

    public void setAxisCalibration(AxesCalibration[] axisCalibration) {
        this.axisCalibration = axisCalibration;
    }

    public int[] getBattery_calibration() {
        return battery_calibration;
    }

    public void setBattery_calibration(int[] battery_calibration) {
        this.battery_calibration = battery_calibration;
    }

    public int getSamplingRate() {
        return samplingRate;
    }

    public void setSamplingRate(int samplingRate) {
        this.samplingRate = samplingRate;
    }    
    
}
