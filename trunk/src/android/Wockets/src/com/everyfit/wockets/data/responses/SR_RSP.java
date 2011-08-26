/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class SR_RSP extends Response {

	public int _SamplingRate = 0;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public SR_RSP(int id) {
		super(id, 2, ResponseTypes.SR_RSP);
		// TODO Auto-generated constructor stub
	}

}
