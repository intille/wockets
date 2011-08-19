package com.everyfit.wockets.apps;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;

import com.everyfit.wockets.WocketsController;
import com.everyfit.wockets.WocketsService;
import com.everyfit.wockets.kernel.KernelCallback;
import com.everyfit.wockets.kernel.KernelListener;
import com.everyfit.wockets.kernel.KernelMessage;
import com.everyfit.wockets.receivers.RFCOMMReceiver;
import com.everyfit.wockets.sensors.AndroidSensor;
import com.everyfit.wockets.sensors.SensorList;
import com.everyfit.wockets.utils.network.NetworkStacks;

import android.app.Activity;
import android.content.Intent;
import android.hardware.Sensor;
import android.hardware.SensorManager;
import android.os.Bundle;
import android.os.Environment;
import android.os.PowerManager;
import android.os.PowerManager.WakeLock;
import android.util.Log;
import android.view.Menu;
import android.view.MenuInflater;
import android.view.MenuItem;
import android.view.WindowManager;
import android.widget.Button;
import android.widget.Toast;

public class CollectData_old extends Activity implements KernelCallback
{
	Button bWocketConnect;
	private static final String TAG = "ServicesDemo";
	private String[] wocketaddress;
	private boolean running = false;
	private String _ROOTPATH = Environment.getExternalStorageDirectory().getAbsolutePath() + "/wockets/";
	
	private SensorManager mSensorManager;
    private PowerManager mPowerManager;
    private WindowManager mWindowManager;
    private WakeLock mWakeLock;
    private float mAccelRange;
    private float mAccelResolution;
    private float mAccelBits;
    private float mAccelNorm;
    private Sensor mAccelerometer;
    
	@Override
	public void onCreate(Bundle savedInstanceState)
	{
		super.onCreate(savedInstanceState);
		
		bWocketConnect = (Button) findViewById(R.id.connect);
		
		KernelListener.callbacks.add(this);
		
		if(Application._Context == null)
		{
			Application._Context = this.getApplicationContext();
			Application._Wockets = new Wockets();
		}
		
		Application._Controller= new WocketsController();
		WocketsService._Context=Application._Context;
		WocketsService._Controller=Application._Controller;
		Application._Controller.Initialize();
		Application._running = true;
		
		Application._Controller.FromXML(this._ROOTPATH + "SensorData.xml");
		SensorList sensorList = Application._Controller._Sensors;
		for(int i = 0 ; i < sensorList.size(); i++)
		{
			if(sensorList.get(i)._Class.equalsIgnoreCase("Wockets"))
				Application._Wockets.add(new Wocket(((RFCOMMReceiver)sensorList.get(i)._Receiver)._Address, sensorList.get(i)._ID));
			else if (sensorList.get(i)._Class.equalsIgnoreCase("Android"))
			{
				mSensorManager = (SensorManager)getSystemService(SENSOR_SERVICE);
		        
		        List<Sensor> sensors = mSensorManager.getSensorList(Sensor.TYPE_ACCELEROMETER);
		        if (sensors.size() > 0) 
		        {
		        	mAccelerometer = sensors.get(0);
		        	mAccelRange = mAccelerometer.getMaximumRange();
		        	mAccelResolution = mAccelerometer.getResolution();
		        	mAccelBits = mAccelRange/mAccelResolution;
		        	mAccelBits = (float) (Math.log10(mAccelBits)/Math.log10(2));        	  
		        	mAccelNorm = (float) ((2* mAccelRange)/(Math.pow(2, mAccelBits)));        	
		        }
		        ((AndroidSensor)sensorList.get(i)).mAccelRange = mAccelRange;
		        ((AndroidSensor)sensorList.get(i)).mAccelResolution = mAccelResolution;
		        ((AndroidSensor)sensorList.get(i)).mAccelBits = mAccelBits;
		        ((AndroidSensor)sensorList.get(i)).mAccelNorm = mAccelNorm;
		        
		        mPowerManager = (PowerManager)getSystemService(POWER_SERVICE);
		        
		        //get instance of window manager
		        mWindowManager = (WindowManager)getSystemService(WINDOW_SERVICE);
		        
		        mWindowManager.getDefaultDisplay();
		        
		        //create bright wake lock
		        mWakeLock = mPowerManager.newWakeLock(PowerManager.SCREEN_BRIGHT_WAKE_LOCK, getClass().getName());
		        mWakeLock.acquire();
		        
		        mSensorManager.registerListener(((AndroidSensor)sensorList.get(i)).mSensorEventListener, mAccelerometer,SensorManager.SENSOR_DELAY_GAME);
			}
				
		}
		
		if (Application._Wockets.size()>0)			
			Application._Controller.Connect(Application._Wockets.toAddressArrayList());
		 else
		 {
			 Toast.makeText(this, "Unable to connect to wockets", Toast.LENGTH_LONG).show();
			 return;
		 }		 
	        
		//set the running variable to true
		running = true; 	
		//Start the WocketsGraph Activity
		Intent i = new Intent();
		i.setClassName("com.everyfit.wockets.apps",
	                      "com.everyfit.wockets.apps.WocketsGraph");
	    startActivity(i);
		
	}
	
	@Override
	protected void onPause() {
		
	    super.onPause();    
	}
	
	@Override
	protected void onResume()
	{
		if(running && Application._running)
		{			
			Intent i = new Intent();
	    	i.setClassName("com.everyfit.wockets.apps",
	                          "com.everyfit.wockets.apps.WocketsGraph");
	        startActivity(i);	        	     			
		}		
		super.onResume();
	}
	
	@Override
	public void finishFromChild(Activity child)
	{
		finish();
	}
	
	@Override
	protected void onDestroy()
	{
		//finish();
		KernelListener.callbacks.remove(this);
		super.onDestroy();
	}
	
	@Override
	public boolean onCreateOptionsMenu(Menu menu)
	{
		MenuInflater inflater = getMenuInflater();
		inflater.inflate(R.menu.wockets_menu,menu);
		return true;
	}
	
	@Override
	public boolean onOptionsItemSelected(MenuItem item)
	{
		switch(item.getItemId())
		{
			case R.id.quit_session:
			{
				quitSession();
				return true;
			}
			default:
			{
				return super.onOptionsItemSelected(item);
			}
		}
	}
	
	public void quitSession()
	{
		
		finish();
	}



	public void OnReceiveKernelMessage(Intent intent) 
	{
		KernelMessage msg=KernelMessage.valueOf(intent.getExtras().getString("KernelMessage"));
		switch(msg)
		{
			case Connected:
				Toast.makeText(this, "Wocket "+intent.getStringExtra("address")+" Connected", Toast.LENGTH_LONG).show();				
				break;
			case Disconnected:
				Toast.makeText(this, "Wocket "+intent.getStringExtra("address")+" disconnected", Toast.LENGTH_LONG).show();				
				break;						
			case Discovered:
				Toast.makeText(this, "Wockets discovery completed", Toast.LENGTH_LONG).show();
				Log.d(TAG, "Discovered");
				//bWocketDiscover.setEnabled(true);				
				Serializable data = intent.getSerializableExtra("table");
				if (data != null) {
					NetworkStacks._BluetoothStack._Discovered = new Hashtable<String, String>((HashMap<String, String>)data);
				}	
				Enumeration<String> e = NetworkStacks._BluetoothStack._Discovered.keys();
				wocketaddress=new String[ NetworkStacks._BluetoothStack._Discovered.size()];
				int i=0;
				while(e.hasMoreElements()){
					wocketaddress[i]=(String)e.nextElement();
					i++;
				}				 
				//lv1.setAdapter(new ArrayAdapter<String>(this,android.R.layout.simple_list_item_multiple_choice , wocketaddress));
				break;
		}
		
	}
		
}
