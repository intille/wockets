package bluetooth;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Vector; 
import javax.bluetooth.DeviceClass;
import javax.bluetooth.DiscoveryAgent;
import javax.bluetooth.DiscoveryListener;
import javax.bluetooth.LocalDevice;
import javax.bluetooth.RemoteDevice;
import javax.bluetooth.ServiceRecord;
import javax.bluetooth.UUID;
import javax.microedition.io.Connector;
import javax.microedition.io.StreamConnection;
import DataCollection.WocketDecoder;
import com.intel.bluetooth.BlueCoveImpl;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.bluetooth.*;


/**
* A simple SPP client that connects with an SPP server
*/
public class PcClient implements DiscoveryListener{
   
    //object used for waiting
    private static Object lock=new Object();
   
    //vector containing the devices discovered
    public static Vector vecDevices = new Vector();
   
    private static String connectionURL=null;
    private static ServiceRecord serviceRecord = null;
    private static java.util.Vector services;
    
    public final static byte[] WOCKET_60_SEC_BURST_PACKET = {(byte) 0xBA, (byte)0x20};
    public final static byte[] WOCKET_Continuous_PACKET = {(byte) 0xBA, (byte)0x00};
    public final static byte[] WOCKET_GET_WTM_PACKET = {(byte) 0xBE};
    public final static byte[] WOCKET_SET_LED_PACKET = {(byte) 0xBC, (byte)0x04}; //Yellow_ LED on for 4 Seconds    
    public final static byte[] WOCKET_SET_TCT_PACKET = {(byte) 0xB9, (byte)0x20, (byte) 0x00, (byte)0x1F, (byte)0x70};
 
    private static PcClient client = new PcClient();
    private static LocalDevice localDevice;
    private static DiscoveryAgent agent; 
    
    public static void findDevices()throws IOException {
    	
        //display local device address and name
        localDevice = LocalDevice.getLocalDevice();
        
        //find devices
        agent = localDevice.getDiscoveryAgent();
      
        //System.out.println("Starting device inquiry...");
        agent.startInquiry(DiscoveryAgent.GIAC, client);
       
        try {
            synchronized(lock){
                lock.wait();
            }
        }
        catch (InterruptedException e) {
            e.printStackTrace();
        }
        //System.out.println("Device Inquiry Completed. ");
       
        //print all devices in vecDevices
        int deviceCount=vecDevices.size();
       
        if(deviceCount <= 0){
            System.out.println("No Devices Found .");
            System.exit(0);
        }
        /*//print bluetooth device addresses and names in the format [ No. address (name) ]
        else{            
            System.out.println("Bluetooth Devices: " + deviceCount);
            for (int i = 0; i <deviceCount; i++) {
            	RemoteDevice remoteDevice=(RemoteDevice)vecDevices.elementAt(i);	                
	        System.out.println((i+1)+". "+remoteDevice.getBluetoothAddress());
            }
        }*/
    }
    
    public static StreamConnection connect(int index)throws IOException{
        //check for spp service
        RemoteDevice remoteDevice=(RemoteDevice)vecDevices.elementAt(index);
        UUID[] uuidSet = new UUID[1];
        uuidSet[0]=new UUID("1101",true);
        int[] attrSet={0x1101}; // Sending this parameter is necessary for connecting to Wockets
        
        System.out.println("\nSearching for service...");
        agent.searchServices(attrSet,uuidSet,remoteDevice,client);
        try {
            synchronized(lock){
                lock.wait();
            }
        }
        catch (InterruptedException e) {
            e.printStackTrace();
        }
          
        if(connectionURL==null){
            System.out.println("Device does not support Simple SPP Service.");
            System.exit(0);
        }
        //connect to the Wocket (as the server) 
        StreamConnection streamConnection=(StreamConnection)Connector.open(connectionURL);
        return streamConnection;
    }
    
    public static void main(String[] args) throws IOException {
       
    	/*findDevices();
       
        System.out.print("Choose Device index: ");
        BufferedReader bReader=new BufferedReader(new InputStreamReader(System.in));
        
        String chosenIndex=bReader.readLine();
        //System.out.println(chosenIndex);
        int index=Integer.parseInt(chosenIndex.trim());
        StreamConnection streamConnection= connect(index-1);
                      
        //write
        OutputStream outStream = streamConnection.openOutputStream();
        outStream.write(WOCKET_Continuous_PACKET);
        
        //read		
        InputStream inStream=streamConnection.openInputStream();
        int cnt = 7;
        byte[] bytes = new byte[cnt];        
        WocketDecoder myDecoder = new WocketDecoder(0);
        SamplingRate sr = new SamplingRate();
        
        Calibrate_SamplingRate(40, inStream,  outStream);
        
        System.out.println("start testing");      
        while (sr.flag < 10){
        	if ((sr.total_time >= 60000)){
    			System.out.print("minute:"+(sr.flag+1));
        		System.out.println("\tSampling Rate: "+ sr.samplingRate);
        		sr.counter = 0;
                        sr.total_time = 0;
                        sr.flag ++;
                }  
        	if (inStream.available() > 0){
        		inStream.read(bytes);
		        myDecoder.Decode(0, bytes, cnt, sr);
        	}
	} */
        
    }//main
    
    //*******************************Calibrate_SamplingRate**********************************************************************
    public static void Calibrate_SamplingRate(double fav_samplingRate, InputStream inStream, OutputStream outStream) throws IOException{
    	byte tct, reps, last;
        double samplingRate = measureSamplingRate(inStream);
        
        if (Math.abs(samplingRate - fav_samplingRate) < 0.13){
            System.out.println("The Wocket is already calibrated: "+samplingRate);
            return;
        }      
        
        System.out.println("Start calibration...");
        System.out.println("The sampling rate before calibration: "+samplingRate);
        double ticks = (int)(7812/fav_samplingRate);//8MHz/2^10=7812
        set_sr(ticks, outStream);     	
    	samplingRate = measureSamplingRate(inStream);
    	double tick1 = ticks;
    	while (Math.abs(samplingRate - fav_samplingRate)> 0.13){
	    	double tick2 = tick1*samplingRate/fav_samplingRate;
	    	if (Math.abs( tick2 - Math.floor(tick2) ) < 0.5)
	    		tick2 = Math.floor(tick2);
	    	else 
	    		tick2 = Math.ceil(tick2);
	    	if (tick2 != tick1){	    		
		    	set_sr(tick2, outStream);		    	
		    	samplingRate = measureSamplingRate(inStream); 
		    	tick1=tick2;
	    	}
	    	else
	    		break;	    	
    	}
    	System.out.println("CAlibration is done. The sampling rate after calibration: "+samplingRate);
    }
    
  //*******************************set_sr************************************************
    public static void set_sr(double ticks, OutputStream outStream) throws IOException{
    	
    	byte tct; byte reps; byte last;
    	if (ticks < 256){ 
        	tct = (byte)(255 - ticks); reps= 0; last= (byte)255;        	 		
        }
        else{
        	tct = 0; reps= (byte)(ticks / 256); last= (byte)(255 - (ticks % 256));
        } 
    	
    	byte[] _Bytes = new byte[] {(byte)0xB9,0,0,0,0};
		_Bytes[1]=(byte) (((byte)tct>>1)&0x7f);
		_Bytes[2]=(byte) ((((byte)tct & 0x01)<<6) | ((byte)reps>>2));
		_Bytes[3]=(byte) ((((byte)reps & 0x03)<<5) |  (byte)((byte)(last>>3) & 0x1f) );
		_Bytes[4]=(byte) (((byte)last & 0x07)<<4);
		for (byte b=0;b<2; b++){
			for (int m=0; m<5; m++){
				//System.out.println(_Bytes[m]);
				outStream.write(_Bytes[m]);
				outStream.flush();
				try {
				Thread.sleep(1000);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
    }
    
	//******************************Measure SR****************************************    
	public static double measureSamplingRate(InputStream inStream)throws IOException{
	    System.out.println("Measuring the Wocket's sampling rate...");
	    SamplingRate sr = new SamplingRate();
	    int cnt = 7;
	    byte[] wocketData = new byte[cnt]; 
	    WocketDecoder myDecoder = new WocketDecoder(0);
	    while (sr.flag < 2){
	            if (sr.total_time >= 60000){
	                    System.out.print("minute:"+(sr.flag+1));
	                    System.out.println("\tSampling Rate: "+ sr.samplingRate);
	                    sr.counter = 0;
	                    sr.total_time = 0;
	                    sr.flag ++;  
	                    //temp_sr = sr.samplingRate;
	            }
	            if (inStream.available() > 0){
	                    inStream.read(wocketData);
	                    myDecoder.Decode(0, wocketData, cnt, sr);    
	            }
	    }  
	    return sr.samplingRate;
	}
    
    //******************************Stop****************************************
    public static void stop(){
        BlueCoveImpl.shutdown();
    }
    
    //******************************methods of DiscoveryListener*******************************************
    @Override
    public void deviceDiscovered(RemoteDevice btDevice, DeviceClass cod) {
    	
        //add the device to the vector
        if((!vecDevices.contains(btDevice)) /*&& (name.contains("Wocket"))*/ ){
            vecDevices.addElement(btDevice);            
        }
    }
    //*************************************************************************
    //implement this method since services are not being discovered
    @Override
    public void servicesDiscovered(int transID, ServiceRecord[] servRecord) {
    	if(servRecord!=null && servRecord.length>0){
            connectionURL=servRecord[0].getConnectionURL(0,false);            
        }
        synchronized(lock){
            lock.notify();
        }
    }
    //*************************************************************************
    //implement this method since services are not being discovered
    public void serviceSearchCompleted(int transID, int respCode) {
        synchronized(lock){
            lock.notify();
        }
    }
    //*************************************************************************
    public void inquiryCompleted(int discType) {
        synchronized(lock){
            lock.notify();
        }
    }  
      
}