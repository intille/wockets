package com.everyfit.wockets.utils.network.bluetooth;

import android.bluetooth.BluetoothAdapter;
import android.os.Parcelable;
import android.content.BroadcastReceiver;
import android.content.Intent;
import android.content.IntentFilter;

import java.util.Hashtable;

import com.everyfit.wockets.WocketsService;

import android.content.Context;
import android.util.Log;
import android.bluetooth.BluetoothDevice;

import com.everyfit.wockets.kernel.*;
import com.everyfit.wockets.utils.CircularBuffer;
import com.everyfit.wockets.utils.network.NetworkStacks;
import com.everyfit.wockets.exceptions.BluetoothException;
public final class BluetoothStack {

	public Hashtable<String,BluetoothStream> _Streams;
	public Hashtable<String,String> _Discovered;
	public static Hashtable<String,BluetoothDevice> _Devices;
	private BluetoothAdapter adapter; 
	public BluetoothStack(){
		_Streams=new Hashtable<String, BluetoothStream>();
		_Discovered=new Hashtable<String,String>();
		_Devices=new Hashtable<String,BluetoothDevice>();
	}
	
	public boolean Initialize()
	{
		adapter=BluetoothAdapter.getDefaultAdapter();
		
		// Register the BroadcastReceiver for the Bluetooth Stack
		IntentFilter filter = new IntentFilter(BluetoothDevice.ACTION_FOUND);	
		filter.addAction(BluetoothAdapter.ACTION_DISCOVERY_FINISHED);
		filter.addAction(BluetoothDevice.ACTION_ACL_CONNECTED);
		filter.addAction(BluetoothDevice.ACTION_ACL_DISCONNECTED);
		filter.addAction("android.bleutooth.device.action.UUID");
	
		WocketsService._Context.registerReceiver(BluetoothStack._CallbackReceiver, filter);		
	    if (adapter == null) 	        
	    	return false;
	    if (!adapter.isEnabled())
	    	return adapter.enable();	
	    else
	    	return true;
	}
	
	// Create a BroadcastReceiver for ACTION_FOUND
	private static final BroadcastReceiver _CallbackReceiver= new BroadcastReceiver() {
	    public void onReceive(Context context, Intent intent) {
	        String action = intent.getAction();
	        Intent myintent=null;
	        try{
	        	
       	  if (action.equals("android.bleutooth.device.action.UUID")) {
	        		  
       		 BluetoothDevice deviceExtra = intent.getParcelableExtra("android.bluetooth.device.extra.DEVICE");
       		 Parcelable[] uuidExtra = intent.getParcelableArrayExtra("android.bluetooth.device.extra.UUID");

       		 action="";
       	  }	  else      	
	        // When discovery finds a device
	        if (BluetoothDevice.ACTION_ACL_CONNECTED.equals(action)) {
	            // Get the BluetoothDevice object from the Intent
	            BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
	            // Add the name and address to an array adapter to show in a ListView
	            String address=device.getAddress();
	            String name=device.getName();
	            myintent = new Intent(WocketsService._Context, KernelListener.class);
				myintent.putExtra("KernelMessage",KernelMessage.Connected.name());
				myintent.putExtra("address",address);
				myintent.putExtra("name",name);
				WocketsService._Context.sendBroadcast(myintent);
	        }
	        else if (BluetoothDevice.ACTION_ACL_DISCONNECTED.equals(action)) {
	            // Get the BluetoothDevice object from the Intent
	            BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);	 
	            // Add the name and address to an array adapter to show in a ListView
	            String address=device.getAddress();
	            String name=device.getName();
	            myintent = new Intent(WocketsService._Context, KernelListener.class);
				myintent.putExtra("KernelMessage",KernelMessage.Disconnected.name());
				myintent.putExtra("address",address);
				myintent.putExtra("name",name);
				WocketsService._Context.sendBroadcast(myintent);
	        }
	        else if (BluetoothDevice.ACTION_FOUND.equals(action)) {
	            // Get the BluetoothDevice object from the Intent
	            BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
	            // Add the name and address to an array adapter to show in a ListView
	            String address=device.getAddress();
	            String name=device.getName();
	           
	            if (!NetworkStacks._BluetoothStack._Discovered.containsKey(address)){
	            	NetworkStacks._BluetoothStack._Discovered.put(address,name);
	            	BluetoothStack._Devices.put(address,device);
	            }
	           
	        }else if (BluetoothAdapter.ACTION_DISCOVERY_FINISHED.equals(action)){	            
	        	myintent = new Intent(WocketsService._Context, KernelListener.class);
				myintent.putExtra("KernelMessage",KernelMessage.Discovered.name());
				myintent.putExtra("table",NetworkStacks._BluetoothStack._Discovered);
				WocketsService._Context.sendBroadcast(myintent);
	        }
	        }catch(Exception e){
	        	Log.e("t", "t");
	        }
	    }
	};
	
	public void Discover(){
		adapter.startDiscovery();
	}
	public BluetoothStream Connect(String address, CircularBuffer rBuffer, CircularBuffer sBuffer)
		throws BluetoothException
	{
		if (!_Devices.containsKey(address)){
			BluetoothDevice device=BluetoothAdapter.getDefaultAdapter().getRemoteDevice(address);
			_Devices.put(address, device);
		}
		BluetoothStream stream=new BluetoothStream(address,rBuffer,sBuffer);
		if (stream._Status == BluetoothStatus.Connected)
		{
			this._Streams.put(address, stream);			
			stream.start();
		}
		return stream;
	}
	
	public void Disconnect(String address){
		if (this._Streams.containsKey(address)){
			this._Streams.get(address).Dispose();
			this._Streams.remove(address);
		}
	}
	public boolean Dispose()
	{
		//Unregister the Broadcast receiver for the Bluetooth Stack
		WocketsService._Context.unregisterReceiver(BluetoothStack._CallbackReceiver);
		if (adapter.isDiscovering())
			adapter.cancelDiscovery();
		boolean result=false;
		if (adapter.isEnabled())
			result=adapter.disable();														
		adapter=null;		
		return result;
	}
	
}