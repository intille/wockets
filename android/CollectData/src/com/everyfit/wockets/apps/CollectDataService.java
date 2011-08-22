package com.everyfit.wockets.apps;

import com.everyfit.wockets.WocketsController;
import com.everyfit.wockets.WocketsService;
import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.Sensor;


import android.app.IntentService;
import android.content.Intent;
import android.os.Handler;
import android.util.Log;
import android.widget.Toast;

public class CollectDataService extends IntentService
{
	private final String TAG = "CollectDataService";
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
		Toast.makeText(WocketsService._Context, "Starting Data Collection", Toast.LENGTH_LONG).show();
		if(Application._running == false)
		{
			stopSelf();	
		}
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
            		sensor.Read();
            	else if (sensor._Receiver._Status==ReceiverStatus.Disconnected)           	
    				sensor.Reconnect();        				        			
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
		super.onDestroy();
	}
}
