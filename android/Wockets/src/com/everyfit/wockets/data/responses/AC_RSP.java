/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public class AC_RSP extends Response {

	 public int _Count;
     public int _SeqNum;
     public double _TimeStamp;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public AC_RSP(int sensorID) {
		// TODO Auto-generated constructor stub
		super((byte)sensorID,6, ResponseTypes.AC_RSP);
	}
	

}
