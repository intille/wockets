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
		if(Application._running == false)
		{
			stopSelf();	
		}
		else
		{
//			Application._Controller.Dispose();
//			Application._Controller= new WocketsController();
//			WocketsService._Context=Application._Context;
//			WocketsService._Controller=Application._Controller;
//			Application._Controller.Initialize();
//			Application._running = true;

		}
		super.onCreate();
	}

	@Override
	protected void onHandleIntent(Intent intent) 
	{
//		Log.d(TAG,"Collect Data Service started");
//		
//		try
//		{
//			mHandler.post(mCollectData);		
//			try
//			{
//				Thread.sleep(20);
//			}
//			catch(InterruptedException ex)
//			{
//				Log.e(TAG,ex.getStackTrace().toString());
//			}
//		}
//		catch(Exception ex)
//		{	
//			Log.e(TAG,"Exception in Collect Data Service");			
//		}
		
		//bToast.makeText(this, "Data Collection Started", Toast.LENGTH_SHORT).show();
		int saveCounter=500;
		while(running)
		{
            for (Sensor sensor:Application._Controller._Sensors)
            {            	  
            	sensor._Receiver.CheckStatus();
            	if (sensor._Receiver._Status==ReceiverStatus.Connected)            		
            		sensor.Read();
            	else if (sensor._Receiver._Status==ReceiverStatus.Disconnected)
            		//check no of reconnection attempts and then display error showing "Unable to connect to wockets"            	
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
            
            try{
            	Thread.sleep(20);
            }catch(Exception e){
            	Log.e(TAG,"Collect Data Service terminated");
            }
		}
	}
	
	@Override
	public void onDestroy()
	{
		//Toast.makeText(this, "Data Collection stopped", Toast.LENGTH_SHORT).show();
		super.onDestroy();
	}
}
