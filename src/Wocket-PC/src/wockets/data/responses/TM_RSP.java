/**
 * 
 */
package wockets.data.responses;

import wockets.data.types.TransmissionMode;

/**
 * @author albinali
 *
 */
public final class TM_RSP extends Response {

	public TransmissionMode _TransmissionMode;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public TM_RSP(int id) {
		super(id, 2, ResponseTypes.TM_RSP);
		// TODO Auto-generated constructor stub
	}

}
