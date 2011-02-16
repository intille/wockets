package com.everyfit.wockets.receivers;

import com.everyfit.wockets.utils.CircularBuffer;
public abstract class Receiver {

	 
 
	public CircularBuffer _Buffer;
	public CircularBuffer _SBuffer;
	public int _ID;
	public ReceiverStatus _Status;
	public Receiver(int id){
		
		this._ID=id;	
		this._Status= ReceiverStatus.Disconnected;
	}
	
    public abstract boolean Initialize();        
    public abstract boolean Dispose();
    public abstract void CheckStatus();
}
