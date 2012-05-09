/**
 * 
 */
package wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class BC_RSP extends Response {

	public int _Count;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public BC_RSP(int id) {
		super(id, 3, ResponseTypes.BC_RSP);
		// TODO Auto-generated constructor stub
	}

}
