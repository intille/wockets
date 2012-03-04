/**
 * 
 */
package wockets.data.responses;

import wockets.data.SensorData;
import wockets.data.SensorDataType;

/**
 * @author albinali
 *
 */
public class Response extends SensorData {

	 public static byte MAX_RAW_BYTES = 10;
	 public ResponseTypes _Type;
	/**
	 * @param sensorID
	 * @param numRawBytes
	 * @param type
	 */
	public Response(int sensorID, int numRawBytes, ResponseTypes type) {
		super(sensorID, numRawBytes, SensorDataType.RESPONSE_PDU);
		// TODO Auto-generated constructor stub
		_Type=type;
	}

}
