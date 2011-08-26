/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class PC_RSP extends Response {

	public int _Count;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public PC_RSP(int id) {
		super(id, 2, ResponseTypes.PDT_RSP);
		// TODO Auto-generated constructor stub
	}

}
