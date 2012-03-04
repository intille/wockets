package bluetooth;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.text.DecimalFormat;
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

import DataCollection.Decoder;
import DataCollection.Logger;
import DataCollection.WocketDecoder;

import wockets.utils.CircularBuffer;
 
/**
* A simple SPP client that connects with an SPP server
*/
public class MyPcClient implements DiscoveryListener{
   
    //object used for waiting
    private static Object lock=new Object();
   
    //vector containing the devices discovered
    private static Vector vecDevices=new Vector();
   
    private static String connectionURL=null;
    private static ServiceRecord serviceRecord = null;
    private static java.util.Vector services;
    
    public final static byte[] WOCKET_60_SEC_BURST_PACKET = {(byte) 0xB3, (byte)0x20};
    public final static byte[] WOCKET_Continuous_PACKET = {(byte) 0xB3, (byte)0x00};
    public final static byte[] WOCKET_GET_WTM_PACKET = {(byte) 0xBE};
    public final static byte[] WOCKET_SET_LED_PACKET = {(byte) 0xBC, (byte)0x03}; //Yellow_ LED on for 31 Seconds
 
    public static void main(String[] args) throws IOException {
       
    	MyPcClient client=new MyPcClient();
       
        //display local device address and name
        LocalDevice localDevice = LocalDevice.getLocalDevice();
        System.out.println("Address: "+localDevice.getBluetoothAddress());
        System.out.println("Name: "+localDevice.getFriendlyName());
       
        //find devices
        DiscoveryAgent agent = localDevice.getDiscoveryAgent();
      
        System.out.println("Starting device inquiry...");
        agent.startInquiry(DiscoveryAgent.GIAC, client);
       
        try {
            synchronized(lock){
                lock.wait();
            }
        }
        catch (InterruptedException e) {
            e.printStackTrace();
        }
         
        System.out.println("Device Inquiry Completed. ");
       
        //print all devices in vecDevices
        int deviceCount=vecDevices.size();
       
        if(deviceCount <= 0){
            System.out.println("No Devices Found .");
            System.exit(0);
        }
        else{
            //print bluetooth device addresses and names in the format [ No. address (name) ]
            System.out.println("Bluetooth Devices: " + deviceCount);
            for (int i = 0; i <deviceCount; i++) {
            	RemoteDevice remoteDevice=(RemoteDevice)vecDevices.elementAt(i);
	            //if (remoteDevice.getFriendlyName(true).contains("Wocket")){	                
	                System.out.println((i+1)+". "+remoteDevice.getBluetoothAddress()/*+" ("+remoteDevice.getFriendlyName(true)+")"*/);
	            //}
            }
        }
       
        System.out.print("Choose Device index: ");
        BufferedReader bReader=new BufferedReader(new InputStreamReader(System.in));
       
        String chosenIndex=bReader.readLine();
        //System.out.println(chosenIndex);
        int index=Integer.parseInt(chosenIndex.trim());
       
        //check for spp service
        RemoteDevice remoteDevice=(RemoteDevice)vecDevices.elementAt(index-1);
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
       
        //write
        OutputStream outStream=streamConnection.openOutputStream();
        /*PrintWriter pWriter=new PrintWriter(new OutputStreamWriter(outStream));
        pWriter.write("Test String from SPP Client\r\n");
        pWriter.flush();*/
        
        //outStream.write(WOCKET_60_SEC_BURST_PACKET);
        outStream.write(WOCKET_Continuous_PACKET);
		outStream.write(WOCKET_SET_LED_PACKET);
		outStream.write(WOCKET_GET_WTM_PACKET);
       
        //read
		
        InputStream inStream=streamConnection.openInputStream();
        int cnt = 10;
        byte[] bytes = new byte[cnt];        
        WocketDecoder myDecoder = new WocketDecoder(0);
        CircularBuffer cBuffer = new CircularBuffer(cnt);
        /*BufferedReader bReader2=new BufferedReader(new InputStreamReader(inStream));
        int cnt = 10;
        byte[] bytes = new byte[cnt];
        char[] chars = new char[cnt];
        int k;*/
        while (true){
	        /*bReader2.read(chars);
	        for (k=0; k<cnt; k++){
	        	bytes[k] = (byte)chars[k];
	        }  */    
        	//inStream.read(cBuffer._Bytes);
        	//myDecoder.Decode(0, cBuffer, 0, cnt);
        	inStream.read(bytes);
	        myDecoder.Decode(0, bytes, cnt);
        	
		}
        
    }//main
    
      
    //methods of DiscoveryListener
    @Override
    public void deviceDiscovered(RemoteDevice btDevice, DeviceClass cod) {
    	/*String name = null; 
    	try{
    	name = btDevice.getFriendlyName(true);
    	}  catch (IOException e) {
    		System.out.println("unable to get name");  
            e.printStackTrace();
        }*/
        //add the device to the vector
        if((!vecDevices.contains(btDevice)) /*&& (name.contains("Wocket"))*/ ){
            vecDevices.addElement(btDevice);            
        }
    }
 
    //implement this method since services are not being discovered
    @Override
    public void servicesDiscovered(int transID, ServiceRecord[] servRecord) {
    	//System.out.println("Number of services:"+ servRecord.length);
        if(servRecord!=null && servRecord.length>0){
            connectionURL=servRecord[0].getConnectionURL(0,false);            
        }
        synchronized(lock){
            lock.notify();
        }
    }
 
    //implement this method since services are not being discovered
    public void serviceSearchCompleted(int transID, int respCode) {
        synchronized(lock){
            lock.notify();
        }
    }
    
    public void inquiryCompleted(int discType) {
        synchronized(lock){
            lock.notify();
        }
    }  
      
}