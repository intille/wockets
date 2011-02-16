package com.everyfit.wockets.apps;


import java.util.ArrayList;

import com.everyfit.wockets.WocketsController;
import com.everyfit.wockets.WocketsService;
import com.everyfit.wockets.data.AccelerationData;
import com.everyfit.wockets.kernel.KernelCallback;
import com.everyfit.wockets.kernel.KernelListener;
import com.everyfit.wockets.kernel.KernelMessage;
import com.everyfit.wockets.sensors.Sensor;

import android.app.Activity;
import android.os.Bundle;
import android.os.Handler;
import android.content.Context;
import android.content.Intent;
import android.view.View;
import android.graphics.Canvas;
import android.graphics.Paint;
import android.graphics.Rect;
import java.util.concurrent.Semaphore;

public class WocketsGraph extends Activity implements Runnable,KernelCallback{

	private GraphicsView view;
	private int NumGraphs=2;
	private int[] tails;
	private boolean running=true;
	private Thread t;
	private static final int MAX_AVAILABLE = 1;
	private final Semaphore available = new Semaphore(MAX_AVAILABLE, true);
	
	public void onCreate(Bundle savedInstanceState) {
		
       super.onCreate(savedInstanceState);
       Application._Controller= new WocketsController();
		 WocketsService._Context=Application._Context;
		 WocketsService._Controller=Application._Controller;
		 Application._Controller.Initialize();
	
		 //Setup the wockets to connect to
		 ArrayList<String> wockets=Application._Wockets.toAddressArrayList();
		 if (Application._Wockets.size()>0)			
				Application._Controller.Connect(Application._Wockets.toAddressArrayList());
		 else
			 return;
		
		tails=new int[Application._Controller._Sensors.size()];
	
		for (int i=0;(i<wockets.size());i++)								
			tails[i]=0;
		       		
       view=new GraphicsView(Application._Context,NumGraphs);
       setContentView(view);              
       //Startup the thread		
	   t=new Thread(this);
	   t.start();
    }
	
	public void onStart(){
		super.onStart();
		//t=new Thread(this);
	}
	public void onPause(){
		  super.onPause();
		  //Stop data callbacks		  
		  KernelListener.callbacks.remove(this);
		  //t.stop();
	}
	
	public void onResume(){
		super.onResume();
		  //Start data callbacks
		KernelListener.callbacks.add(this);
		//t.start();
				
	}
	

	public class GraphicsView extends View{
		
		public ArrayList<Integer> IDs=new ArrayList<Integer>();
		public ArrayList<Integer> Xs=new ArrayList<Integer>();
		public ArrayList<Integer> Ys=new ArrayList<Integer>();
		public ArrayList<Integer> Zs=new ArrayList<Integer>();
		public int Width;
		public int Height;
		public int[] position;
		public int[] offset;
		
		private Paint black;
		private Paint red;
		private Paint green;

		private int[] prevX;
		private int[] prevY;
		private int[] prevZ;
		private float scalingFactor=0;
		private int NumGraphs=0;
		
		public GraphicsView(Context context, int numGraphs){		
			super(context);		
			Width=this.getWidth();
			Height=this.getHeight();	
			black=new Paint();
			black.setColor(getResources().getColor(R.color.BLACK));
			red=new Paint();
			red.setColor(getResources().getColor(R.color.RED));
			green=new Paint();
			green.setColor(getResources().getColor(R.color.GREEN));
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
		protected void onDraw(Canvas canvas){

			for(int i=0;(i<IDs.size());i++)
			{			
				try{
				int id=(int)IDs.get(i);
				int x=(int)(Xs.get(i)*scalingFactor)+offset[id];
				int y=(int)(Ys.get(i)*scalingFactor)+offset[id];
				int z=(int)(Zs.get(i)*scalingFactor)+offset[id];
				
				if (prevX[id]>=0)
				{
					canvas.drawLine(position[id], prevX[id], position[id]+1, x, black);
					canvas.drawLine(position[id], prevY[id], position[id]+1, y, red);
					canvas.drawLine(position[id], prevZ[id], position[id]+1, z, green);
				}
				
				prevX[id]=x;
				prevY[id]=y;
				prevZ[id]=z;
				position[id]=position[id]+1;
				
				/*if (position[id]>(Width-1))
					position[id]=0;*/
				}catch (Exception e){
					System.out.print("");
				}
				
				
			}
			IDs.clear();
			Xs.clear();
			Ys.clear();
			Zs.clear();
	
			
		}
				
	}
	

	int id=0;
	int x=0;
	int y=0;
	int z=0;
	
    final Runnable mUpdateInterface = new Runnable() {
        public void run() {
        	        	        	
        	int[] pointCount=new int[Application._Controller._Sensors.size()];
    		for(int i=0;(i<Application._Controller._Sensors.size());i++)
    			{					
    			try{
    				Sensor sensor=Application._Controller._Sensors.get(i);
     				int head=sensor._Decoder._Head;
     				pointCount[i]=0;
    				while(tails[i]!=head){
    					AccelerationData datum=((AccelerationData)sensor._Decoder._Data[tails[i]]);				
    					id= datum._SensorID;    					
    					view.IDs.add(id);
    					x= (int) datum._X;
    					view.Xs.add(x);
    					y= (int) datum._Y;
    					view.Ys.add(y);
    					z= (int) datum._Z;
    					view.Zs.add(z);																			
    					pointCount[i]=pointCount[i]+1;
    					
    					tails[i]=tails[i]+1;
    					if (tails[i]==sensor._Decoder._Data.length)
    						tails[i]=0;
    				}
    				
    			}catch(Exception e){
    				System.out.print("");
    			}
    	
    			
    		
    			}
    		
    		
    		for(int i=0;(i<Application._Controller._Sensors.size());i++)
			{					
		
    		int start=view.position[i];
    		int end=view.position[i]+pointCount[i];
    		if (end>view.Width){
    			view.position[0]=0;
    			view.position[1]=0;
    			view.invalidate();
    		}else{
    		    			
    			view.invalidate(new Rect(start,view.offset[0],end,view.offset[1]));    			
				view.invalidate(new Rect(start,view.offset[1],end,view.Height));
			
    		}
	
			}	
			
        }
    };
	
    final Handler mHandler = new Handler();
	public void run() {
		
		while(running){
					
			mHandler.post(mUpdateInterface);		
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	
	public void OnReceiveKernelMessage(Intent intent)
	{

				
	}

}
