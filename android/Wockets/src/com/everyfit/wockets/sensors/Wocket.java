/**
 * 
 */
package com.everyfit.wockets.sensors;


import com.everyfit.wockets.receivers.RFCOMMReceiver;
import com.everyfit.wockets.decoders.WocketDecoder;

/**
 * @author albinali
 *
 */
public class Wocket extends Sensor {

	/**
	 * 
	 */
	public Wocket(int id,String address,String storagePath) {
		// TODO Auto-generated constructor stub
		super(id,storagePath);
		this._Receiver=new RFCOMMReceiver(id,address);
		this._Receiver.Initialize();
		this._Decoder= new WocketDecoder(id);
		this._Decoder.Initialize();
	}

 
    
    @Override
    public synchronized void Reconnect()
    {    	
    	((RFCOMMReceiver)this._Receiver).Reconnect();
  
    }
}
