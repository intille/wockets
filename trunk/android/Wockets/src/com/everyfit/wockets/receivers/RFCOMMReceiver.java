package com.everyfit.wockets.receivers;

import android.util.Log;

import com.everyfit.wockets.utils.CircularBuffer;


import java.util.ArrayList;
import com.everyfit.wockets.data.commands.Command;
import com.everyfit.wockets.data.commands.SET_VTM;
import com.everyfit.wockets.data.types.TransmissionMode;
import com.everyfit.wockets.exceptions.BluetoothException;
import com.everyfit.wockets.utils.network.NetworkStacks;
import com.everyfit.wockets.utils.network.bluetooth.BluetoothStatus;
import com.everyfit.wockets.utils.network.bluetooth.BluetoothStream;;

public final class RFCOMMReceiver extends Receiver {

		
	private final String TAG = "RFCOMMReceiver";
     private static final int BUFFER_SIZE = 16834;	
	 private static final int SEND_BUFFER_SIZE = 256;	
	 public String _Address;
	 public ArrayList<Command> _OnConnectionCommands = new ArrayList<Command>();
	 public TransmissionMode _TransmissionMode=  TransmissionMode.Continuous;
	 public BluetoothStream _BluetoothStream;
     public long _CurrentConnectionUnixTime = 0;
     public int _Reconnections = 0;
     public int _SuccessfulConnections = 0;
     public ReconnectionThread reconnectionThread=null;
     
	 
     public RFCOMMReceiver(int id,String address)
     {    
    	 super(id);     
    	 this._Address=address;
    	 
     }
     
     
     
     public boolean Initialize(){
     
    	
    	 if (this._Buffer==null)
    		 this._Buffer = new CircularBuffer(BUFFER_SIZE);
    	 if (this._SBuffer==null)
    		 this._SBuffer = new CircularBuffer(SEND_BUFFER_SIZE);

         //Always set the transmission mode on connection      
         for (int i = 0; (i < this._OnConnectionCommands.size()); i++)
             Write(this._OnConnectionCommands.get(i)._Bytes);
         this._OnConnectionCommands.clear();         
         Write(new SET_VTM(this._TransmissionMode)._Bytes);

         try
         {
        	 this._BluetoothStream = NetworkStacks._BluetoothStack.Connect(this._Address,this._Buffer,this._SBuffer);
         }
         catch(BluetoothException e){
        	 Log.d(TAG, e.toString());
        	
         }
         if (this._BluetoothStream  == null)
             return false;
         else if (this._BluetoothStream._Status==BluetoothStatus.Disconnected)
         {
        	 this._BluetoothStream.Dispose();
        	 return false;
         }
         
         //for reconnection
//         if(this._BluetoothStream == null)
//         {
//        	 if(this._Reconnections < 3)
//        	 {
//        		 this._Reconnections++;
//        		 Reconnect();
//        	 }
//        	 else
//        	 {
//        		 return false;
//        	 }
//        	 
//        	 
//         }
         
         this._CurrentConnectionUnixTime = this._BluetoothStream._CurrentConnectionUnixTime;
         this._SuccessfulConnections++;
         this._Status= ReceiverStatus.Connected;                 
         reconnectionThread=null;
         return true;               
     }
     
     public synchronized void Reconnect(){    	    
    	 this._Status= ReceiverStatus.Reconnecting;
    	 if (reconnectionThread!=null)
    		 reconnectionThread.Dispose();
    	 reconnectionThread=new ReconnectionThread(this);
    	 reconnectionThread.start();
     }
     
     public synchronized int getReconnections()
     {
    	 return this._Reconnections;
     }
     
     @Override
     public synchronized void CheckStatus(){
    	 try{
    		 if ((this._Status==ReceiverStatus.Connected)&&(this._BluetoothStream._Status==BluetoothStatus.Disconnected))
    		 {
    			 this._BluetoothStream.Dispose();
    			 this._BluetoothStream=null;
    			 this._Status=ReceiverStatus.Disconnected;    		    			 
    		 }    		
    	 }catch(Exception e)
    	 {
    		 
    	 }
     }
     
    class ReconnectionThread extends Thread
    {
    	private com.everyfit.wockets.receivers.RFCOMMReceiver receiver;
    	private boolean running=true;
    	public ReconnectionThread(com.everyfit.wockets.receivers.RFCOMMReceiver receiver){
    		this.receiver=receiver;
    	}    	    	
    	public void run(){
    		while ((this.receiver._Status==ReceiverStatus.Reconnecting) && (running) )
    		{    		
    			this.receiver.Initialize();
    		}
    			    			    		    		
    	}
    	
    	public void Dispose(){
    		running=false;
    		try {
				this.join();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
    	}
    	
    }
     public synchronized void Write(byte[] data)
     {

        int availableBytes = data.length;        
        //only insert if the send buffer won't overflow
        if ((this._SBuffer._Tail + availableBytes) > this._SBuffer._Bytes.length)
        {
        	CircularBuffer.BlockCopy(data, 0, this._SBuffer._Bytes, this._SBuffer._Tail, this._SBuffer._Bytes.length - this._SBuffer._Tail);
            availableBytes -= this._SBuffer._Bytes.length - this._SBuffer._Tail;
            this._SBuffer._Tail = 0;
         }
        
        CircularBuffer.BlockCopy(data, data.length - availableBytes, this._SBuffer._Bytes, this._SBuffer._Tail, availableBytes);
        this._SBuffer._Tail += availableBytes; 
         
     }
     public boolean Dispose(){
    	 if (reconnectionThread!=null)
    		 reconnectionThread.Dispose(); 
    	 this._BluetoothStream.Dispose();
    	 NetworkStacks._BluetoothStack. Disconnect(this._Address);//.Disconnect
    	 return true;
     }
               
}
