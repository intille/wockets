package com.everyfit.wockets.kernel;

import 	android.content.BroadcastReceiver;
import android.content.Intent;
import android.content.Context;
import android.util.Log;
import java.util.ArrayList;



public class KernelListener extends BroadcastReceiver {

	public static ArrayList<KernelCallback> callbacks=new ArrayList<KernelCallback>();
	
    // Display an alert that we've received a message.    
    @Override 
    public void onReceive(Context context, Intent intent)
    {  	  	
    	try
    	{        		
    		for(KernelCallback c : callbacks)
    			c.OnReceiveKernelMessage(intent);
    	}
    	catch(Exception e)
    	{    		
    		Log.e("error", e.getMessage());
    	}    
    }
}
