/**
 * 
 */
package wockets.data.responses;

/**
 * @author albinali
 *
 */
public final class BTCAL_RSP extends Response {

    public int _CAL100;
    public int _CAL80;
    public int _CAL60;
    public int _CAL40;
    public int _CAL20;
    public int _CAL10;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public BTCAL_RSP(int id) {
		super((byte)id,10, ResponseTypes.BTCAL_RSP);
		// TODO Auto-generated constructor stub
	}

}
