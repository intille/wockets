/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class OFT_RSP extends Response {

	public int _Offset;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public OFT_RSP(int id) {
		super(id, 3, ResponseTypes.OFT_RSP);
		// TODO Auto-generated constructor stub
	}

}
