package com.everyfit.wockets.apps;

import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.Sensor;

import android.app.Service;
import android.content.Intent;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.IBinder;
import android.os.Looper;
import android.os.Message;
import android.os.Process;
import android.util.Log;
import android.widget.Toast;

public class DataService extends Service
{
	private final String TAG = "DataService";
	private Looper mServiceLooper;
	private ServiceHandler mServiceHandler;
	private boolean running = true;
	
	private final class ServiceHandler extends Handler
	{
		public ServiceHandler(Looper looper)
		{
			super(looper);
		}
		
		@Override
		public void handleMessage(Message msg)
		{
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
	            		sensor.Save();            		
	            	}
	            		            	
	            	saveCounter=500;
	            }
	            
	            try{
	            	Thread.sleep(20);
	            }catch(Exception e){
	            	Log.e(TAG,"Exception in Data service");
	            	Log.e(TAG, e.getStackTrace().toString());
	            }
			}
			
			stopSelf(msg.arg1);
		}
	}
	
	@Override
	public void onCreate()
	{
		HandlerThread thread = new HandlerThread("CollectDataService",Process.THREAD_PRIORITY_BACKGROUND);
		thread.start();
		mServiceLooper = thread.getLooper();
		mServiceHandler = new ServiceHandler(mServiceLooper);
	}
	
	@Override
	public int onStartCommand(Intent intent, int flags, int startId)
	{
		Toast.makeText(this,"Data Collection Started",Toast.LENGTH_SHORT).show();
		
		Message msg  = mServiceHandler.obtainMessage();
		msg.arg1 = startId;
		mServiceHandler.sendMessage(msg);
		
		//restart if killed 
		return START_NOT_STICKY;
		//return START_STICKY;
	}
	
	@Override
	public void onDestroy()
	{
		Toast.makeText(this, "Data Collection Terminated", Toast.LENGTH_SHORT).show();
		running = false;
		Application._running = false;
		super.onDestroy();
	}
	
	@Override
	public IBinder onBind(Intent arg0) {
		// does not provide binding
		return null;
	}

}


