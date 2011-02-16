package com.everyfit.wockets.kernel;


import java.util.ArrayList;

import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.util.Log;

public class ApplicationListener extends BroadcastReceiver {
	//public static ApplicationCallback callback=null;
	public static ArrayList<ApplicationCallback> callbacks=new ArrayList<ApplicationCallback>();
    // Display an alert that we've received a message.    
    @Override 
    public void onReceive(Context context, Intent intent)
    {
    	try
    	{    
    		for(ApplicationCallback c : callbacks)
    			c.OnReceiveApplicationMessage(intent);
    		//if (callback!=null){    			
    			//callback.OnReceiveApplicationMessage(intent);
    	//	}
    	}
    	catch(Exception e)
    	{    
    		Log.e("t","t");
    	}
    }
}
