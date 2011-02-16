/**
 * 
 */
package com.everyfit.wockets.data.responses;
import com.everyfit.wockets.data.types.Sensitivity;

/**
 * @author albinali
 *
 */
public final class SENS_RSP extends Response {

	public Sensitivity _Sensitivity;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public SENS_RSP(int id) {
		super(id, 2, ResponseTypes.SENS_RSP);
		// TODO Auto-generated constructor stub
	}

}
