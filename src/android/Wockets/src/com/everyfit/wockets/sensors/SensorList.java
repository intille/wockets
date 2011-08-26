/**
 * 
 */
package com.everyfit.wockets.sensors;

import java.util.ArrayList;


/**
 * @author albinali
 *
 */
public final class SensorList extends ArrayList<Sensor> {

	public SensorList(){
		
	}
	
	public void Dispose(){
		for (Sensor sensor:this)
			sensor.Dispose();
	}
}
