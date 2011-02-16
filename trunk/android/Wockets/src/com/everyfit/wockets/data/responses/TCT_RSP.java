/**
 * 
 */
package com.everyfit.wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class TCT_RSP extends Response {

	  public int _TCT;
      public int _REPS;
      public int _LAST;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public TCT_RSP(int id) {
		super(id, 5, ResponseTypes.TCT_RSP);
		// TODO Auto-generated constructor stub
	}

}
