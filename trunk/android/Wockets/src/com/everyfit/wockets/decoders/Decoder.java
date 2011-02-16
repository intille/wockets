/**
 * 
 */
package com.everyfit.wockets.decoders;

import com.everyfit.wockets.data.SensorData;
import com.everyfit.wockets.utils.CircularBuffer;

/**
 * @author albinali
 *
 */
public abstract class Decoder {

	
    public SensorData[] _Data;
    public SensorData[] _Response;
    protected byte[] packet;
    public int _Head;
    public int _ID;
    public int IX;
	/**
	 * 
	 */
	public Decoder(int id, int bufferSize, int packetSize) {
		// TODO Auto-generated constructor stub
		this._Data = new SensorData[bufferSize];  
		this._Response=new SensorData[10];
		this.packet= new byte[packetSize];
		this._ID=id;
	}
	
    public abstract int Decode(int sensorID, CircularBuffer data, int start,int end);

    public abstract boolean Initialize();        
    public abstract boolean Dispose();
}
