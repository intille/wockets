/**
 * 
 */
package DataCollection;




/**
 * @author albinali
 *
 */
public class Wocket extends Sensor {

	/**
	 * 
	 */
	public Wocket(int id,String address,String storagePath) {
	
		super(id,storagePath);
		this._Class = "Wockets";
		this._Receiver=new RFCOMMReceiver(id,address);
		this._Decoder= new WocketDecoder(id);
	}
	
    
    @Override
    public synchronized void Reconnect()
    {    	
    	((RFCOMMReceiver)this._Receiver).Reconnect();
  
    }
}
