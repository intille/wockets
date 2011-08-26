package com.everyfit.wockets.utils.network;

import com.everyfit.wockets.utils.network.bluetooth.*;
import android.util.Log;

public class NetworkStacks {

	private static final String TAG = "NetworkStacks";
	public static BluetoothStack _BluetoothStack=null;	
	
	public NetworkStacks() {

	}
	
	public void Initialize()
	{		
		_BluetoothStack=new BluetoothStack();
		if (!_BluetoothStack.Initialize())
			Log.d(TAG, "Failed to initialize bluetooth stack");
	}
	
	 public void Dispose() 
	 { 
		 if (_BluetoothStack!=null)
			 _BluetoothStack.Dispose(); 
	 }	
}
