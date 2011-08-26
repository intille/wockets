/**
 * 
 */
package com.everyfit.wockets.data.responses;

import com.everyfit.wockets.data.SensorData;
import com.everyfit.wockets.data.SensorDataType;

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
