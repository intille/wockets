package com.everyfit.wockets;


import java.util.Calendar;
import java.util.Hashtable;
import java.util.ArrayList;
import java.util.SimpleTimeZone;
import java.lang.Thread;
import java.text.DecimalFormat;


import android.app.AlarmManager;
import android.os.Environment;

import com.everyfit.wockets.utils.network.*;
import com.everyfit.wockets.data.types.TransmissionMode;
import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.SensorList;
import com.everyfit.wockets.sensors.Sensor;
import com.everyfit.wockets.sensors.Wocket;


public class WocketsController  extends Thread{
	private final String TAG = "WocketsController";	
	public NetworkStacks _Network;
	public Hashtable<String,String> _SelectedWockets;
	public TransmissionMode _TransmissionMode;
	public SensorList _Sensors;
	public String _RootPath="";	
	public String _DataStoragePath="";
	private boolean running=true;
	public WocketsController(){	
		//Need to add support for other media
		this._RootPath=Environment.getExternalStorageDirectory().getAbsolutePath()+"/wockets/";		
	}
		
	public void run() {
		
		int saveCounter=500;
		while(running)
		{
            for (Sensor sensor:this._Sensors)
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
            	for (Sensor sensor:this._Sensors)
            		sensor.Save();            	
            	saveCounter=500;
            }
            
            try{
            	Thread.sleep(20);
            }catch(Exception e){
            	
            }
		}
	}
	public void Initialize() {
		this._TransmissionMode=TransmissionMode.Continuous;
		_Network=new NetworkStacks();
		_Network.Initialize();			
	}

	public void Discover(){
		NetworkStacks._BluetoothStack.Discover();
	}
	public void Connect(ArrayList<String> wockets){
		
		int index=0;
		this._Sensors=new SensorList();
		long nowms=(System.currentTimeMillis()-(AlarmManager.INTERVAL_HOUR*5));
	    Calendar now = Calendar.getInstance(new SimpleTimeZone(0, "GMT"));	   
	    now.setTimeInMillis(nowms);
	    DecimalFormat twoPlaces = new DecimalFormat("00");

		this._DataStoragePath=this._RootPath+"Session-" + twoPlaces.format(now.get(Calendar.MONTH)) + "-" + twoPlaces.format(now.get(Calendar.DAY_OF_MONTH)) + "-" + now.get(Calendar.YEAR) + "-" + twoPlaces.format(now.get(Calendar.HOUR_OF_DAY)) + "-" + twoPlaces.format(now.get(Calendar.MINUTE)) + "-" + twoPlaces.format(now.get(Calendar.SECOND))+"/";
		for(String address: wockets){
			Wocket sensor=new Wocket(index,address,this._DataStoragePath);
			this._Sensors.add(sensor);					
			index++;
		}		
		this.start();		
	}
	
	public void Disconnect(){
		for(Sensor sensor:this._Sensors)
			sensor.Dispose();
		this.stop();
	}
	
	public void Dispose(){
		running=false;		
		try {
			this.join();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		if (this._Sensors!=null){
			for(Sensor sensor:this._Sensors){
				sensor._Decoder.Dispose();
				sensor._Receiver.Dispose();
			}
		}
		
		_Network.Dispose();
	}
	
}
