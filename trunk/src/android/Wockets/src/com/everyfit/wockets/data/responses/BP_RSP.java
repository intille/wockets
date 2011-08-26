/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class BP_RSP extends Response {

	public int _Percent;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public BP_RSP(int id) {
		super((byte)id,3, ResponseTypes.BP_RSP);
		// TODO Auto-generated constructor stub
	}

}
