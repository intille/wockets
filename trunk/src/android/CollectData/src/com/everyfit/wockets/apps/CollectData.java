package com.everyfit.wockets.apps;

import java.util.ArrayList;
import java.util.List;

import com.everyfit.wockets.WocketsController;
import com.everyfit.wockets.WocketsService;
import com.everyfit.wockets.data.AccelerationData;
import com.everyfit.wockets.kernel.KernelCallback;
import com.everyfit.wockets.kernel.KernelListener;
import com.everyfit.wockets.kernel.KernelMessage;
import com.everyfit.wockets.receivers.RFCOMMReceiver;
import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.AndroidSensor;
import com.everyfit.wockets.sensors.SensorList;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.SharedPreferences;
import android.graphics.Canvas;
import android.graphics.Paint;
import android.hardware.Sensor;
import android.hardware.SensorManager;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.PowerManager;
import android.os.PowerManager.WakeLock;
import android.util.Log;
import android.view.Display;
import android.view.Menu;
import android.view.MenuInflater;
import android.view.MenuItem;
import android.view.View;
import android.view.WindowManager;
import android.widget.AdapterView;
import android.widget.ArrayAdapter;
import android.widget.ListView;
import android.widget.Toast;

public class CollectData extends Activity implements Runnable,KernelCallback
{	
	private static final String TAG = "Collect Data";
	public static final String PREF_FILE_NAME = "WocketsPrefFile";
	private boolean running = false;
	private String _ROOTPATH = Environment.getExternalStorageDirectory().getAbsolutePath() + "/wockets/";
	private String _SensorData = "SensorData_1.xml";
	private int sensorSet = 1;
	private boolean prefRunning = false;
	
	private SensorManager mSensorManager;
    private PowerManager mPowerManager;
    private WindowManager mWindowManager;
    private Display mDisplay;
    private WakeLock mWakeLock;
    private float mAccelRange;
    private float mAccelResolution;
    private float mAccelBits;
    private float mAccelNorm;
    private Sensor mAccelerometer;       
    
    // variables for graph
    private GraphicsView view;
	private int NumGraphs=0;
	private int[] tails;	
	private Thread t;	
	
	Canvas canvas;
	
	public int[] position;
	public int[] offset;
	private float scalingFactor = 0;
	
	private Paint blue;
	private Paint red;
	private Paint green;
	private Paint[] arrPaints;
	
	private int[] prevX;
	private int[] prevY;
	private int[] prevZ;
	
	int id;
	int x;
	int y;
	int z;
	
	final Handler mHandler = new Handler();
	
	
	ArrayList<int[]> canvasPoints;

    
	@Override
	public void onCreate(Bundle savedInstanceState)
	{		
		super.onCreate(savedInstanceState);
			
		KernelListener.callbacks.add(this);
		
		SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);
		SharedPreferences.Editor editor = preferences.edit();					
		prefRunning =  preferences.getBoolean("running", false);
		
		if(prefRunning == false)
		{				
			ArrayList<String> arrAlert = new ArrayList<String>();
			arrAlert.add("Green Set");
			arrAlert.add("Red Set");
			
			final AlertDialog.Builder builder = new AlertDialog.Builder(this);
			final ListView listView = new ListView(this);		
			listView.setChoiceMode(ListView.CHOICE_MODE_SINGLE);		
			listView.setAdapter(new ArrayAdapter<String>(this,android.R.layout.simple_list_item_single_choice,arrAlert));
			listView.setItemChecked(0, true);
			listView.setOnItemClickListener(new AdapterView.OnItemClickListener() {

				public void onItemClick(AdapterView<?> myAapter, View myView, int myItem,
						long myLong)
				{
					String selected = (String) listView.getItemAtPosition(myItem);
					if(selected.equalsIgnoreCase("Green Set"))
					{
						sensorSet = 1;
						_SensorData = "SensorData_1.xml";					
					}
					else
					{
						sensorSet = 2;
						_SensorData = "SensorData_2.xml";
					}
				}
				
			});
			
			builder.setMessage("Select the Wocket Set :");
			builder.setView(listView);
			builder.setPositiveButton("Ok", new DialogInterface.OnClickListener() {
				
				public void onClick(DialogInterface dialog, int which) 
				{				
					SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);
					SharedPreferences.Editor editor = preferences.edit();
					if (sensorSet == 2)
					{
						editor.putInt("sensorSet", 2);			
					}
					else
					{
						editor.putInt("sensorSet", 1);			
					}						
									
					editor.commit();
									
					Application._SensorData = _SensorData;
					
					startSession();
				}
			});
			
			builder.setNegativeButton("Cancel", new DialogInterface.OnClickListener() {
				
				public void onClick(DialogInterface dialog, int which) 
				{
					finish();				
				}
			});
			
			builder.show();						
		}
		else
		{
			if(Application._Context == null )
			{				
				prefRunning =  false;
				editor.putBoolean("running", prefRunning);
				editor.commit();
			}
			startSession();
		}					
	}
	
	@Override
	protected void onPause() 
	{	
		mUpdateInterface = null;
		t = null;
		running = false;
	    super.onPause();    
	    
	}
	
	@Override
	protected void onResume()
	{	
		super.onResume();
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
			case R.id.swap:
			{
				swapWockets();
				return true;
			}
			default:
			{
				return super.onOptionsItemSelected(item);
			}
		}
	}
	
	public void startSession()
	{		
		
		if(prefRunning == false)
		{
			prefRunning = true;
			SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);		
			SharedPreferences.Editor editor = preferences.edit();
			editor.putBoolean("running", prefRunning);			
			editor.commit();
			
			Application._Context = this.getApplicationContext();
			Application._Wockets = new Wockets();
			Application._Controller= new WocketsController();
			WocketsService._Context=Application._Context;
			WocketsService._Controller=Application._Controller;
			Application._Controller.Initialize(this._SensorData);
			Application._running = true;
			
			Application._Controller.FromXML(this._ROOTPATH + this._SensorData);
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
			        
			        //get instance of Display
			        mDisplay = mWindowManager.getDefaultDisplay();
			        
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
		        
			
		}
		 	
		//Start the WocketsGraph Activity
		
		//set the running variable to true
		running = true;
		Application._running = true;
		
		ArrayList<String> wockets=Application._Wockets.toAddressArrayList();
		tails=new int[Application._Controller._Sensors.size()];
		
		for (int i=0;(i<wockets.size());i++)								
			tails[i]=0;
		canvasPoints = new ArrayList<int[]>();
		
	   NumGraphs = Application._Controller._Sensors.size();	   	  	   
	   view=new GraphicsView(Application._Context,NumGraphs);
	   setContentView(view);              
	   
	   //Startup the thread       
	   t=new Thread(this);
	   t.start();	
	   
	   //clear
	   wockets.clear();
	   wockets = null;
	}
	
	public void swapWockets()
	{	
			final AlertDialog.Builder alert = new AlertDialog.Builder(this);
			alert.setMessage("Are you sure you want to swap wockets?");
			alert.setNegativeButton("No", new DialogInterface.OnClickListener() {
				
				public void onClick(DialogInterface dialog, int which) 
				{					
					return;
				}
			});
			
			alert.setPositiveButton("Yes", new DialogInterface.OnClickListener() {
				
				public void onClick(DialogInterface dialog, int which)
				{
					try
					{
						t = null;
						running = false;
						Application._running = false;
						
						prefRunning = false;
						SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);		
						SharedPreferences.Editor editor = preferences.edit();
						editor.putBoolean("running", prefRunning);			
						editor.commit();
						
						for(int i = 0 ; i < Application._Controller._Sensors.size(); i++)
						{
							if(Application._Controller._Sensors.get(i)._Class.equalsIgnoreCase("Android"))
							{
								AndroidSensor sensor = (AndroidSensor)Application._Controller._Sensors.get(i);
								mSensorManager.unregisterListener(sensor.mSensorEventListener);
							}
						}
						
						Intent intent = new Intent();
						intent.setClassName("com.everyfit.wockets.apps", "com.everyfit.wockets.apps.CollectDataService");
						stopService(intent);
						
						Application._Controller.Dispose();
						Application._running = false;
						Application._Context = null;
						Application._Wockets.clear();
						Application._Controller = null;		
						
						mUpdateInterface = null;
						t = null;
					
						finish();
									
						
						Thread.sleep(3000);
						
						
						preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);
						int sensorSet = preferences.getInt("sensorSet", 0);
						editor = preferences.edit();
						
						if (sensorSet == 2)
						{
							sensorSet = 1;
							editor.putInt("sensorSet", 1);				
						}
						else
						{
							sensorSet = 2;
							editor.putInt("sensorSet", 2);				
						}		
										
						editor.commit();
						
						_SensorData = "SensorData_" + sensorSet + ".xml";
						Application._SensorData = _SensorData;			
						
						intent = new Intent();
						intent.setClassName("com.everyfit.wockets.apps", "com.everyfit.wockets.apps.CollectData");
						startActivity(intent);

					}
					catch(Exception ex)
					{
						Log.e(TAG,"Error in swapping wockets");
					}														
				}
			});
			alert.show();
	}
	
	public void quitSession()
	{
		final AlertDialog.Builder alert = new AlertDialog.Builder(this);
		alert.setMessage("Are you sure you want to quit?");
		alert.setNegativeButton("No", new DialogInterface.OnClickListener() {
			
			public void onClick(DialogInterface dialog, int which) 
			{					
				return;
			}
		});
		
		alert.setPositiveButton("Yes", new DialogInterface.OnClickListener() {
			
			public void onClick(DialogInterface dialog, int which) 
			{
				for(int i = 0 ; i < Application._Controller._Sensors.size(); i++)
				{
					if(Application._Controller._Sensors.get(i)._Class.equalsIgnoreCase("Android"))
					{
						AndroidSensor sensor = (AndroidSensor)Application._Controller._Sensors.get(i);
						mSensorManager.unregisterListener(sensor.mSensorEventListener);
					}
				}
						
				
				Intent intent = new Intent();
				intent.setClassName("com.everyfit.wockets.apps", "com.everyfit.wockets.apps.CollectDataService");
				stopService(intent);												
				
				running = false;
				prefRunning = false;
				SharedPreferences preferences = getSharedPreferences(PREF_FILE_NAME, MODE_PRIVATE);
				SharedPreferences.Editor editor = preferences.edit();
				editor.putBoolean("running", prefRunning);
				editor.clear();
				editor.commit();
				
				//clear the Application object
				Application._Controller.Dispose();
				Application._running = false;
				Application._Context = null;
				Application._Wockets.clear();
				Application._Controller = null;		
				
				mUpdateInterface = null;
				t = null;
				
				finish();
				
			}
		});
		
		alert.show();
		
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
				break;
		}
		
	}
	
	public class GraphicsView extends View
	{			
		public int Width;
		public int Height;		
		private int NumGraphs=0;	
		
		public GraphicsView(Context context, int numGraphs)
		{		
			super(context);		
			Width=this.getWidth();
			Height=this.getHeight();	
			
			blue=new Paint();
			blue.setColor(getResources().getColor(R.color.BLUE));
			red=new Paint();
			red.setColor(getResources().getColor(R.color.RED));
			green=new Paint();
			green.setColor(getResources().getColor(R.color.GREEN));
			
			arrPaints = new Paint[]{blue,red,green};
			
			position=new int[numGraphs];
			offset=new int[numGraphs];
			prevX=new int[numGraphs];
			prevY=new int[numGraphs];
			prevZ=new int[numGraphs];
			for (int i=0;(i<numGraphs);i++)
			{
				position[i]=0;
				prevX[i]=0;
				prevY[i]=0;
				prevZ[i]=0;
			}
			NumGraphs=numGraphs;			
		}
		
	
		@Override
		protected void onSizeChanged(int w,int h,int oldw,int oldh){
			Width=w;
			Height=h;
			scalingFactor=Height/NumGraphs/(float)1024;
			for (int i=0;(i<NumGraphs);i++)
				offset[i]=i*Height/NumGraphs;
			super.onSizeChanged(w, h, oldw, oldh);
		}
		protected void onDraw(Canvas canvas)
		{			
			if(mUpdateInterface != null && t != null)
			{	
				int[] points;
				for(int i = 0; i < canvasPoints.size(); i++)
				{
					points = canvasPoints.get(i);
					canvas.drawLine(points[0], points[1], points[2], points[3], arrPaints[points[4]]);
				}
				
				//clear
				points = null;
			}
		}		
	}

	public Thread mUpdateInterface = new Thread() 
    {
        public void run() 
        {
        	if (t != null)
        	{        		
        		int[] pointCount=new int[Application._Controller._Sensors.size()];
        		int[] points;        		
        		for(int i=0;(i<Application._Controller._Sensors.size());i++)
        		{        			
    				try
        			{        				
        				com.everyfit.wockets.sensors.Sensor sensor=Application._Controller._Sensors.get(i);
        				if(sensor._Receiver._Status == ReceiverStatus.Connected)        					
        				{                 			        					
        					if(sensor._Class.equalsIgnoreCase("Android"))
        					{
        						AndroidSensor andSensor = (AndroidSensor)sensor;
        						int head = 0;
        						ArrayList<float[]> AccelerationData = andSensor.mRawData;
        						float[] data;
        						
        						while(head != AccelerationData.size() -1 )
        						{
        							id = andSensor._ID;        							
        							
        							data = andSensor.mRawData.get(head);
        							x = (int) ((andSensor.mAccelRange + data[0]) / (andSensor.mAccelNorm));        				
        							x = (int) ((x * scalingFactor)  + offset[id]);
        							points = new int[]{position[id],prevX[id],position[id]+1,x,0};
        							canvasPoints.add(points);
        							
        							y = (int) ((andSensor.mAccelRange + data[1]) / (andSensor.mAccelNorm));;
        							y = (int) ((y * scalingFactor)  + offset[id]);
        							points = new int[]{position[id],prevY[id],position[id]+1,y,1};
        							canvasPoints.add(points);
        							
        							z = (int) ((andSensor.mAccelRange + data[2]) / (andSensor.mAccelNorm));;
        							z = (int) ((z * scalingFactor)  + offset[id]);
        							points = new int[]{position[id],prevZ[id],position[id]+1,z,2};
        							canvasPoints.add(points);
        							
        							prevX[id] = x;
        							prevY[id] = y;
        							prevZ[id] = z;
        							position[id]=position[id]+1;			
        							
        							pointCount[i]=pointCount[i]+1;
                					
                					tails[i]=tails[i]+1;
                					if (tails[i]==sensor._Decoder._Data.length)
                						tails[i]=0;
                					
                					int start = position[i];
                					int end = position[i] + pointCount[i];
                					
                					if(end > view.Width)
                					{      
                     					for(int j = 0 ; j < NumGraphs ; j ++)
                    	    			{
                    	    				position[j] = 0 ;
                    	    				pointCount[i]=0;
                    	    			}                	    				
                	    				view.invalidate();
                	    				canvasPoints.clear();
                					}
                					else
                					{
                						if( (i+1) < NumGraphs)
                						{
                							view.invalidate(start,offset[i],end,offset[i+1]);
                						}
                							
                						else
                						{
                							view.invalidate(start,offset[NumGraphs-1],end,view.Height);
                						}            							            						            					
                					}            			
                					head++;
        						}
        						AccelerationData.clear();
        						andSensor = null;
        						data = null;
        					}
        					else
        					{
                 				int head=sensor._Decoder._Head;
                				while(tails[i]!=head)
                				{                					                					                					                					                				
                					AccelerationData datum=((AccelerationData)sensor._Decoder._Data[tails[i]]);				
                					id= datum._SensorID;    					            									            			
                					
                					x= (int) ((((int) datum._X) * scalingFactor) + offset[id]);
                					points = new int[]{position[id],prevX[id],position[id]+1, x,0};
                					canvasPoints.add(points);            					            				
                					
                					y= (int) ((((int) datum._Y) * scalingFactor) + offset[id]);            				
                					points = new int[]{position[id],prevY[id],position[id]+1, y,1};
                					canvasPoints.add(points);            					
                					
                					z= (int) ((((int) datum._Z) * scalingFactor) + offset[id]);            					                					
                					points = new int[]{position[id],prevZ[id],position[id]+1, z,2};
                					canvasPoints.add(points);                					
                					
                					prevX[id]=x;
            						prevY[id]=y;
            						prevZ[id]=z;
            						position[id]=position[id]+1;				
            						
                					pointCount[i]=pointCount[i]+1;
                					
                					tails[i]=tails[i]+1;
                					if (tails[i] == sensor._Decoder._Data.length)
                						tails[i]=0;
                					
                					int start = position[i];
                					int end = position[i] + pointCount[i];            					

                     				if(end > view.Width)
                					{      
                     					for(int j = 0 ; j < NumGraphs ; j ++)
                    	    			{
                    	    				position[j] = 0 ;
                    	    				pointCount[i]=0;
                    	    			}                	    				
                	    				view.invalidate();
                	    				canvasPoints.clear();
                					}
                					else
                					{
                						if( (i+1) < NumGraphs)
                						{
                							view.invalidate(start,offset[i],end,offset[i+1]);
                						}
                							
                						else
                						{
                							view.invalidate(start,offset[NumGraphs-1],end,view.Height);
                						}            							            						            					
                					}            					            				
                				}
        					}
                				                				
        				}
        			}
        			catch(Exception e)
        			{        				
        				Log.e(TAG,"error in mUpdateInterface thread");        			
        			}        			        		
        		}
        		
        		//clear
        		points = null;
        		pointCount = null;
        	}    			    		
        }
    };
 

	public void run() 
	{		
		while(running)
		{					
			mHandler.post(mUpdateInterface);		
			try 
			{
				Thread.sleep(150);
			}
			catch (InterruptedException e) 
			{	
				e.printStackTrace();
			}					
		}
	}
		
}
