/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class HV_RSP extends Response {

	public int _Version = 0;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public HV_RSP(int id) {
		super(id, 2, ResponseTypes.HV_RSP);
		// TODO Auto-generated constructor stub
	}

}
