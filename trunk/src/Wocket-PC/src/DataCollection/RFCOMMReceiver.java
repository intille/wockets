package DataCollection;

//import android.util.Log;

import wockets.utils.CircularBuffer;


import java.util.ArrayList;
import wockets.data.commands.Command;
import wockets.data.commands.CommandTypes;
import wockets.data.commands.Commands;
import wockets.data.types.TransmissionMode;
//import wockets.exceptions.BluetoothException;
//import wockets.utils.network.NetworkStacks;
//import wockets.utils.network.bluetooth.BluetoothStatus;
//import wockets.utils.network.bluetooth.BluetoothStream;;

public final class RFCOMMReceiver extends Receiver {

		
	private final String TAG = "RFCOMMReceiver";
     private static final int BUFFER_SIZE = 16834;	
	 private static final int SEND_BUFFER_SIZE = 256;	
	 public String _Address;
	 public ArrayList<Command> _OnConnectionCommands = new ArrayList<Command>();
	 public TransmissionMode _TransmissionMode=  TransmissionMode.Continuous;
	// public BluetoothStream _BluetoothStream;
     public long _CurrentConnectionUnixTime = 0;
     public int _Reconnections = 0;
     public int _SuccessfulConnections = 0;
     public ReconnectionThread reconnectionThread=null;
     
	 
     public RFCOMMReceiver(int id,String address)
     {    
    	 super(id);     
    	 this._Address=address;
    	 
     }
     
     
     
     public synchronized boolean Initialize()
     {
     
    	
    	 if (this._Buffer==null)
    		 this._Buffer = new CircularBuffer(BUFFER_SIZE);
    	 if (this._SBuffer==null)
    		 this._SBuffer = new CircularBuffer(SEND_BUFFER_SIZE);

         //Always set the transmission mode on connection      
         for (int i = 0; (i < this._OnConnectionCommands.size()); i++)
             Write(this._OnConnectionCommands.get(i)._Bytes);
         this._OnConnectionCommands.clear();         
        // Write(new SET_VTM(this._TransmissionMode)._Bytes);
         Commands c = new Commands();
         c.call(CommandTypes.SetWocketTransmissionMode, this._TransmissionMode);

       /*  try
         {
        	 this._BluetoothStream = NetworkStacks._BluetoothStack.Connect(this._Address,this._Buffer,this._SBuffer);
         }
         catch(BluetoothException e)
         {
        	         	
         }
         if (this._BluetoothStream  == null)
             return false;
         else if (this._BluetoothStream._Status==BluetoothStatus.Disconnected)
         {
        	 this._BluetoothStream.Dispose();
        	 return false;
         }
         
         this._CurrentConnectionUnixTime = this._BluetoothStream._CurrentConnectionUnixTime;
         this._SuccessfulConnections++;
         this._Status= ReceiverStatus.Connected;                 
         reconnectionThread=null;*/
         return true;               
     }
     
     /*public synchronized void Reconnect(){    	    
    	 this._Status= ReceiverStatus.Reconnecting;
    	 if (reconnectionThread!=null)
    		 reconnectionThread.Dispose();
    	 
    	 reconnectionThread = null;
    	 reconnectionThread=new ReconnectionThread(this);    	 
    	 reconnectionThread.start();
     }*/
     
    public synchronized void Reconnect()
     {
//    	this._Status = ReceiverStatus.Reconnecting;
//    	NetworkStacks._BluetoothStack.Disconnect(this._Address);//.Disconnect
//    	if(this._BluetoothStream != null)
//    		this._BluetoothStream.Dispose();    
//    	this.Initialize();    	
     }
     
     public synchronized int getReconnections()
     {
    	 return this._Reconnections;
     }
     
     @Override
     public synchronized void CheckStatus(){
    	/* try{
    		 if ((this._Status==ReceiverStatus.Connected)&&(this._BluetoothStream._Status==BluetoothStatus.Disconnected))
    		 {
    			 this._BluetoothStream.Dispose();
    			 this._BluetoothStream=null;
    			 this._Status=ReceiverStatus.Disconnected;    		    			 
    		 }    		
    	 }catch(Exception e)
    	 {
    		 
    	 }*/
     }
     
    class ReconnectionThread extends Thread
    {
    	private RFCOMMReceiver receiver;
    	private boolean running=true;
    	public ReconnectionThread(RFCOMMReceiver receiver){
    		this.receiver=receiver;
    	}    	    	
    	public void run()
    	{
    		while ((this.receiver._Status==ReceiverStatus.Reconnecting) && (running) )
    		//while (this.receiver._Status==ReceiverStatus.Reconnecting)
    		{
    			if(Thread.interrupted())
    				break;
    			/*NetworkStacks._BluetoothStack.Disconnect(this.receiver._Address);//.Disconnect
    	    	 if(this.receiver._BluetoothStream != null)
    	    		 this.receiver._BluetoothStream.Dispose();    */	 
    	    	try
    	    	{
    	    		Thread.sleep(200);
    	    	}
    	    	catch(InterruptedException ex)
    	    	{
    	    		
    	    	}
    			this.receiver.Initialize();    			
    		}
    			    			    		    		
    	}
    	
    	public void Dispose()
    	{
    			
    		//if(this.receiver._Status == ReceiverStatus.Reconnecting && running)
    		{
    			try 
        		{    			
    				this.interrupt();
    			}
    			catch (SecurityException e) 
    			{    			

    			}
    		}
    		this.receiver._Status = ReceiverStatus.Disconnected;    	
    		
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
     public boolean Dispose()
     {
    	 if (reconnectionThread!=null)
    	 {    		 
    		 reconnectionThread.Dispose();
    		 
    		 this._Status = ReceiverStatus.Disconnected;     		    
    		 reconnectionThread = null;    		 
    	 }    		      	
    	 reconnectionThread = null;
    	 /*NetworkStacks._BluetoothStack.Disconnect(this._Address);//.Disconnect
    	 if(this._BluetoothStream != null)
    		 this._BluetoothStream.Dispose();   */ 	 
    	 return true;
     }
               
}
