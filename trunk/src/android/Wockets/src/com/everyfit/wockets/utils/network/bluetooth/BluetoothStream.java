package com.everyfit.wockets.utils.network.bluetooth;

import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothSocket;

import java.util.ArrayList;
import java.util.UUID;
import 	java.lang.Thread;
import java.lang.reflect.Method;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import com.everyfit.wockets.utils.CircularBuffer;
import com.everyfit.wockets.utils.network.NetworkStacks;
import com.everyfit.wockets.exceptions.BluetoothException;
import android.os.Process;
import android.util.Log;

import 	java.util.concurrent.CyclicBarrier;

public final class BluetoothStream extends Thread{

	private final String TAG = "BluetoothStream";
	private final BluetoothSocket mmSocket;
    private final BluetoothDevice mmDevice;
    private InputStream mmInStream=null;
    private OutputStream mmOutStream=null;

    // Unique UUID for this application
    private static final UUID MY_UUID = UUID.fromString("00001101-0000-1000-8000-00805F9B34FB");
    
    public ArrayList<UUID> ARR_UUIDS;
    private CircularBuffer rBuffer;
    private CircularBuffer sBuffer;
    public long _CurrentConnectionUnixTime = 0;
    public BluetoothStatus _Status= BluetoothStatus.Disconnected;
    public boolean _EnableTimeout=true;
    public int _Timeout=200;
    private int currentTimeout=0;
   
	public BluetoothStream(String address,CircularBuffer rBuffer,CircularBuffer sBuffer)
		throws BluetoothException
	{			
		
		// Use a temporary object that is later assigned to mmSocket,
        // because mmSocket is final
        BluetoothSocket tmp = null;
     
       
        //mmDevice = BluetoothStack._Devices.get(address);
        mmDevice = BluetoothAdapter.getDefaultAdapter().getRemoteDevice(address);
        // Get a BluetoothSocket to connect with the given BluetoothDevice
        try 
        {
            ////tmp = mmDevice.createRfcommSocketToServiceRecord(MY_UUID);        	
        	Method m = mmDevice.getClass().getMethod("createRfcommSocket", new Class[] {int.class});
        	tmp = (BluetoothSocket) m.invoke(mmDevice, 1);
        	//tmp = mmDevice.createInsecureRfcommSocketToServiceRecord(MY_UUID);
        }
        catch 
        (Exception e) 
        { 
        	throw new BluetoothException("Constructor:BluetoothStream:createRfcommSocketToServiceRecord",e.getStackTrace().toString(),e.getMessage());
        }
        mmSocket = tmp;                     
        this.rBuffer=rBuffer;
        this.sBuffer=sBuffer;
        
        try 
        {
            // Connect the device through the socket. This will block
            // until it succeeds or throws an exception
        	BluetoothAdapter.getDefaultAdapter().cancelDiscovery();
        	if(mmSocket != null)
        	{
        		mmSocket.connect();
        	}
                        
        } 
        catch (IOException connectException) 
        {
            // Unable to connect; close the socket and get out
            try 
            {
                mmSocket.close();
            } 
            catch (IOException closeException) 
            { 
                throw new BluetoothException("Constructor:BluetoothStream:close",closeException.getStackTrace().toString(),closeException.getMessage());
            }            
            throw new BluetoothException("Constructor:BluetoothStream:connect",connectException.getStackTrace().toString(),connectException.getMessage());            
        }
        
        this._CurrentConnectionUnixTime= System.currentTimeMillis();        
        InputStream tmpIn = null;
        OutputStream tmpOut = null;

        // Get the input and output streams, using temp objects because
        // member streams are final
        try 
        {
            tmpIn = mmSocket.getInputStream();            
        } 
        catch (IOException e) 
        { 
        	throw new BluetoothException("Constructor:BluetoothStream:getInputStream",e.getStackTrace().toString(),e.getMessage());
        }

        mmInStream = tmpIn;
        
        try 
        {            
            tmpOut = mmSocket.getOutputStream();
        } 
        catch (IOException e) 
        { 
        	throw new BluetoothException("Constructor:BluetoothStream:getOutputStream",e.getStackTrace().toString(),e.getMessage());
        }        
        mmOutStream = tmpOut;
        this._Status = BluetoothStatus.Connected;
	}
		
	private int LOCAL_BUFFER_SIZE = 2048;
    private int sentBytes = 0;
    private int totalBytes = 0;
    protected int pollingInterval = 20;
    
    public synchronized int Read(byte[] singleReadBuffer) throws IOException{
    	return mmInStream.read(singleReadBuffer, 0, LOCAL_BUFFER_SIZE);
    }
    
    
    public  synchronized void Write(byte[] sendByte) throws IOException{
    	 mmOutStream.write(sendByte); 
    }
	 public void run() {
         byte[] sendByte = new byte[1];         
         byte[] singleReadBuffer = new byte[LOCAL_BUFFER_SIZE];
         android.os.Process.setThreadPriority(android.os.Process.THREAD_PRIORITY_URGENT_AUDIO);

         while (this._Status == BluetoothStatus.Connected)
         {            
             int bytesReceived = 0;
             try
             {              
                 // Transmit data if needed 1 byte at a time, for a maximum of 10 bytes in each iteration
                 // then receive to avoid substantial delays
            	 int counter = 0;
                 while (this.sBuffer._Tail != this.sBuffer._Head)
                 {
                     sendByte[0] = this.sBuffer._Bytes[this.sBuffer._Head];                     
                     Write(sendByte);                  
                     sentBytes++;
                     if (this.sBuffer._Head >= (this.sBuffer._Bytes.length - 1))
                        this.sBuffer._Head = 0;
                     else
                        this.sBuffer._Head++;                                              
                     counter++;
                     if (counter == 10)
                        break;
                  }
                 int length=mmInStream.available();
                 if (length>0){
                	 bytesReceived =  Read(singleReadBuffer);
                     totalBytes += bytesReceived;
                 }
   

                 // Sleep for a specific length of time, defaults to 30 milliseconds
                 Thread.sleep(30);
               

                 // Timeout if data is not received within a specific time, defaults to 12 seconds
                 if (_EnableTimeout)
                 {
                     if (bytesReceived > 0)
                    	 currentTimeout = 0;
                     else
                     {
                    	 currentTimeout++;
                         if (currentTimeout > _Timeout)
                         {       
                             this._Status = BluetoothStatus.Disconnected;
                             break;
                         }
                     }
                 }
             }
             catch (Exception e)
             {                 
                 this._Status = BluetoothStatus.Disconnected;
                 break;
             }

             // Copy received bytes to a non-local referenced buffer
             int ii;
             int mytail = this.rBuffer._Tail;
             for (ii = 0; ii < bytesReceived; ii++)
             {
                 this.rBuffer._Bytes[mytail++] = singleReadBuffer[ii];
                 mytail %= this.rBuffer._Bytes.length;                                       
             }
             this.rBuffer._Tail =mytail;
         }
	 }
	 
	 public void Dispose()
	 {			 
		 this._Status=BluetoothStatus.Disconnected;
		 try
		 {
			 this.join();
		 }
		 catch (Exception e)
		 {			
		 }
		 try
		 {
			 mmInStream.close();
			 mmOutStream.close();
		 }
		 catch(IOException ex)
		 {
			 Log.e(TAG,"Exception while closing streams");
		 }
		 try 
		 {			 	            
			 mmSocket.close();	       
		 } 
		 catch (IOException e) 
		 { 
			 Log.e(TAG,"Exception while closing socket");
		 }
	 }

}
