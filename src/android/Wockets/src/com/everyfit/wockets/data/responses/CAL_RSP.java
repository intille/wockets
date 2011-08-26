/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class CAL_RSP extends Response {

    public int _X1G;
    public int _XN1G;
    public int _Y1G;
    public int _YN1G;
    public int _Z1G;
    public int _ZN1G;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public CAL_RSP(int id) {
		super((byte)id,10, ResponseTypes.CAL_RSP);
		// TODO Auto-generated constructor stub
	}

}
