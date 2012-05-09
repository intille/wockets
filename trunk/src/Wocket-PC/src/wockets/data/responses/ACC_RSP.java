/**
 * 
 */
package wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class ACC_RSP extends Response {

	public int _Count;
	/**
	 * 
	 */
	public ACC_RSP(int id) {
		// TODO Auto-generated constructor stub
		super((byte)id,3, ResponseTypes.ACC_RSP);
	}

}
