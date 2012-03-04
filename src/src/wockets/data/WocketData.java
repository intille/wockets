/**
 * 
 */
package wockets.data;

/**
 * @author albinali
 *
 */
public final class WocketData extends AccelerationData {

	
	public static int NUM_RAW_BYTES = 5;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public WocketData(int sensorID) {
		super(sensorID, NUM_RAW_BYTES);
		// TODO Auto-generated constructor stub
	}

}
