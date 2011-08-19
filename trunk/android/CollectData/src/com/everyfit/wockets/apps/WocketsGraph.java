package com.everyfit.wockets.apps;


import java.util.ArrayList;
import com.everyfit.wockets.data.AccelerationData;
import com.everyfit.wockets.kernel.KernelCallback;
import com.everyfit.wockets.kernel.KernelListener;
import com.everyfit.wockets.receivers.ReceiverStatus;
import com.everyfit.wockets.sensors.Sensor;
import android.app.Activity;
import android.os.Bundle;
import android.os.Handler;
import android.content.Context;
import android.content.Intent;
import android.util.Log;
import android.view.Menu;
import android.view.MenuInflater;
import android.view.MenuItem;
import android.view.View;
import android.graphics.Canvas;
import android.graphics.Paint;


public class WocketsGraph extends Activity implements Runnable,KernelCallback{
	
	private final String TAG = "WocketsGraph";
	private GraphicsView view;
	private int NumGraphs=0;
	private int[] tails;
	private volatile boolean running=true;
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

	public void onCreate(Bundle savedInstanceState)
	{
		
       super.onCreate(savedInstanceState);		 
		
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
	public void onStart()
	{
		super.onStart();				
	}
	
	@Override
	public void onPause()
	{		  		  
		//Stop data callbacks		
		try
		{
			mUpdateInterface = null;			
			t = null;
		}
		catch(Exception ex)
		{
			Log.e(TAG,"Exception while stopping threads");
		}
		  running = false;	
		KernelListener.callbacks.remove(this);
		super.onPause();
		
		finish();		  
	}
	
	@Override
	public void onResume()
	{		
		//Start data callbacks
		running = true;
		KernelListener.callbacks.add(this);
		super.onResume();			
	}	
		
	
	@Override
	public void onSaveInstanceState(Bundle outState)
	{
		super.onSaveInstanceState(outState);
	}
	
	@Override
	public void onRestoreInstanceState(Bundle savedInstanceState)
	{
		super.onRestoreInstanceState(savedInstanceState);
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
		if(running)
		{
			Application._Controller.Dispose();
			
			Intent intent = new Intent();
			intent.setClassName("com.everyfit.wockets.apps", "com.everyfit.wockets.apps.DataService");
			stopService(intent);										
			
			running = false;
			Application._running = false;
			
			mUpdateInterface = null;
			t = null;
			
			KernelListener.callbacks.remove(this);			
			finish();
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
        				Sensor sensor=Application._Controller._Sensors.get(i);
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
	
	public void OnReceiveKernelMessage(Intent intent)
	{

				
	}
	
	
}
