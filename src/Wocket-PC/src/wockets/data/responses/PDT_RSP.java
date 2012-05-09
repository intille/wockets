/**
 * 
 */
package wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class PDT_RSP extends Response {

	public int _Timeout = 0;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public PDT_RSP(int id) {
		super(id, 6, ResponseTypes.PC_RSP);
		// TODO Auto-generated constructor stub
	}

}
