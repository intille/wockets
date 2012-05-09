/**
 * 
 */
package wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class FV_RSP extends Response {

	public int _Version = 0;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public FV_RSP(int id) {
		super(id, 2, ResponseTypes.FV_RSP);
		// TODO Auto-generated constructor stub
	}

}
