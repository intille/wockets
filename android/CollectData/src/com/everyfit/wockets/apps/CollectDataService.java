package com.everyfit.wockets.apps;

import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.Sensor;


import android.app.IntentService;
import android.content.Intent;
import android.content.SharedPreferences;
import android.os.Bundle;
import android.os.Handler;
import android.util.Log;
import android.widget.Toast;

public class CollectDataService extends IntentService
{
	private final String TAG = "CollectDataService";
	public static final String PREF_FILE_NAME = "WocketsPrefFile";

	private boolean running = true;
	final Handler mHandler = new Handler();
	
	public CollectDataService() 
	{
		
		super("CollectDataService");
		setIntentRedelivery(true);
	}
	
	@Override
	public void onCreate()
	{	
		SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);
		SharedPreferences.Editor editor = preferences.edit();
		running = preferences.getBoolean("running", false);
				
		if(running == false)
		{
			stopSelf();	
		}
		Log.d(TAG, "running in data service=" + running);
		Toast.makeText(Application._Context, "Starting Data Collection", Toast.LENGTH_LONG).show();
		
		super.onCreate();
	}

	@Override
	protected void onHandleIntent(Intent intent) 
	{

		int saveCounter=500;
		while(running && Application._running)
		{
            for (Sensor sensor:Application._Controller._Sensors)
            {            	  
            	sensor._Receiver.CheckStatus();
            	if (sensor._Receiver._Status==ReceiverStatus.Connected)
            	{
            		sensor.Read();
            	}            		
            	else if (sensor._Receiver._Status==ReceiverStatus.Disconnected)
            	{        			
              		sensor.Reconnect(); 
            	}            		        				        		
            }
            
            //Save and flush data infrequently
            if (saveCounter--<0)
            {
            	for (Sensor sensor:Application._Controller._Sensors)
            	{
            		if (sensor._Receiver._Status==ReceiverStatus.Connected)
            			sensor.Save();            		
            	}
            		            	
            	saveCounter=500;
            }
            
            try
            {
            	Thread.sleep(20);
            }
            catch(Exception e)
            {
            	Log.e(TAG,"Collect Data Service terminated");
            }
		}
	}
	
	
	
	@Override
	public void onDestroy()
	{
		SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);
		SharedPreferences.Editor editor = preferences.edit();
		editor.clear();
		editor.commit();
		
		super.onDestroy();
	}
}
