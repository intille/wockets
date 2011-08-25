/**
 * 
 */
package com.everyfit.wockets;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;


import com.everyfit.wockets.kernel.ApplicationCallback;
import com.everyfit.wockets.kernel.ApplicationListener;
import com.everyfit.wockets.kernel.ApplicationMessage;
import com.everyfit.wockets.kernel.KernelListener;
import com.everyfit.wockets.kernel.KernelMessage;

import android.content.Context;
import android.app.Service;
import android.content.Intent;
import android.os.IBinder;

/**
 * @author albinali
 *
 */
public final class WocketsService extends Service implements ApplicationCallback {

	public static WocketsController _Controller;
	public static Context _Context;
	public static final boolean DEBUG = true;

	
	public void OnReceiveApplicationMessage(Intent intent)
	{
		Intent myintent;
		ApplicationMessage msg=ApplicationMessage.valueOf(intent.getExtras().getString("ApplicationMessage"));
		switch(msg)
		{						
			case Ping: 		
				myintent = new Intent(this, KernelListener.class);
				myintent.putExtra("KernelMessage",KernelMessage.Running.name());
				sendBroadcast(myintent);
				break;
			case Discover:					
				_Controller.Discover();
				break;
			case Connect:					
				Serializable data = intent.getSerializableExtra("selectedwockets");
				if (data != null) 
					_Controller._SelectedWockets=new Hashtable<String, String>((HashMap<String, String>)data);
				ArrayList<String> ee =new ArrayList<String>();				
				Enumeration<String> e = _Controller._SelectedWockets.keys();
				int i=0;
				while(e.hasMoreElements()){
					String s=((String)e.nextElement()).toUpperCase();				
					ee.add(s);
					i++;
				}		
				
				_Controller.Connect(ee);
				break;				
		}		
	}
	
	
	@Override
    public void onCreate() {    
		  _Context=this.getApplicationContext();
          _Controller= new WocketsController();
          _Controller.Initialize("SensorData.xml");        
    }

	@Override
	public void onStart(Intent intent, int startid) {
		//ApplicationListener.callback=this;
		ApplicationListener.callbacks.add(this);
		Intent myintent = new Intent(this, KernelListener.class);
		myintent.putExtra("KernelMessage",KernelMessage.Started.name());
		sendBroadcast(myintent);
	}
	
	public void onDestroy() {
		Intent intent = new Intent(this, KernelListener.class);
		intent.putExtra("KernelMessage",KernelMessage.Stopped.name());
		sendBroadcast(intent);
		//ApplicationListener.callback=null;
		ApplicationListener.callbacks.remove(this);
		_Controller.Dispose();
		_Controller=null;
	}
	/* (non-Javadoc)
	 * @see android.app.Service#onBind(android.content.Intent)
	 */
	@Override
	public IBinder onBind(Intent arg0) {
		// TODO Auto-generated method stub
		return null;
	}

}
