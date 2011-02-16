/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class BL_RSP extends Response {

	public int _BatteryLevel;
	/**
	 * 
	 */
	public BL_RSP(int id) {
		// TODO Auto-generated constructor stub
		super((byte)id,3, ResponseTypes.BL_RSP);
	}

}
