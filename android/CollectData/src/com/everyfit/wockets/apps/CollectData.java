package com.everyfit.wockets.apps;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;

import com.everyfit.wockets.WocketsController;
import com.everyfit.wockets.WocketsService;
import com.everyfit.wockets.apps.WocketsGraph.GraphicsView;
import com.everyfit.wockets.data.AccelerationData;
import com.everyfit.wockets.kernel.KernelCallback;
import com.everyfit.wockets.kernel.KernelListener;
import com.everyfit.wockets.kernel.KernelMessage;
import com.everyfit.wockets.receivers.RFCOMMReceiver;
import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.AndroidSensor;
import com.everyfit.wockets.sensors.SensorList;
import com.everyfit.wockets.utils.network.NetworkStacks;

import android.app.Activity;
import android.content.Context;
import android.content.Intent;
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
import android.widget.Button;
import android.widget.ListView;
import android.widget.Toast;

public class CollectData extends Activity implements Runnable,KernelCallback
{
	Button bWocketConnect;
	private static final String TAG = "ServicesDemo";
	private ListView lv1;
	private String[] wocketaddress;
	private Hashtable<String,String> selectedwockets;
	private ArrayList<String> selWockets;
	private boolean running = false;
	private int requestCode = 1;
	private String _ROOTPATH = Environment.getExternalStorageDirectory().getAbsolutePath() + "/wockets/";
	
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
		
		bWocketConnect = (Button) findViewById(R.id.connect);
		
		KernelListener.callbacks.add(this);
		
		if(Application._Context == null)
		{
			Application._Context = this.getApplicationContext();
			Application._Wockets = new Wockets();
		}
		
		if(Application._running == false)
		{
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
		
		ArrayList<String> wockets=Application._Wockets.toAddressArrayList();
		tails=new int[Application._Controller._Sensors.size()];
		
		for (int i=0;(i<wockets.size());i++)								
			tails[i]=0;
		canvasPoints = new ArrayList<int[]>();
		
	   NumGraphs = wockets.size();	   	  	   
	   view=new GraphicsView(Application._Context,NumGraphs);
	   setContentView(view);              
	   
	   //Startup the thread       
	   t=new Thread(this);
	   t.start();
		
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
			default:
			{
				return super.onOptionsItemSelected(item);
			}
		}
	}
	
	public void quitSession()
	{
		Application._Controller.Dispose();
		
		Intent intent = new Intent();
		intent.setClassName("com.everyfit.wockets.apps", "com.everyfit.wockets.apps.DataService");
		stopService(intent);										
		
		running = false;
		Application._running = false;
		
		mUpdateInterface = null;
		t = null;
		
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
	
	public class GraphicsView extends View
	{
		
		public ArrayList<Integer> IDs=new ArrayList<Integer>();
		public ArrayList<Integer> Xs=new ArrayList<Integer>();
		public ArrayList<Integer> Ys=new ArrayList<Integer>();
		public ArrayList<Integer> Zs=new ArrayList<Integer>();
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
             				int head=sensor._Decoder._Head;
            				while(tails[i]!=head)
            				{                					                					                					                					                				
            					AccelerationData datum=((AccelerationData)sensor._Decoder._Data[tails[i]]);				
            					id= datum._SensorID;    					
            					view.IDs.add(id);            					            				
            					
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
        			catch(Exception e)
        			{        				
        				Log.e(TAG,"error in mUpdateInterface thread");
        			}        			        		
        		}        		        		
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
