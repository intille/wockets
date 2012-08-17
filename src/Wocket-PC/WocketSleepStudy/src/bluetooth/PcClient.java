
package bluetooth;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.text.SimpleDateFormat;
import java.util.Vector; 
import javax.bluetooth.DeviceClass;
import javax.bluetooth.DiscoveryAgent;
import javax.bluetooth.DiscoveryListener;
import javax.bluetooth.LocalDevice;
import javax.bluetooth.RemoteDevice;
import javax.bluetooth.ServiceRecord;
import javax.bluetooth.UUID;
import javax.bluetooth.BluetoothConnectionException;
import javax.microedition.io.Connector;
import javax.microedition.io.StreamConnection;

import java.text.ParseException;

import bafFormat.BafDecoder;
import bafFormat.RawDataFileHandler;
import bafFormat.SummaryDataFileHandler;

import com.intel.bluetooth.BlueCoveImpl;

import decoder.WocketDecoder;

import java.net.Socket;
import java.util.Calendar;
import java.util.Date;
import javax.swing.JTextArea;
import wockets.data.WocketParam;

/**
* A simple SPP client that connects with an SPP server
*/
public class PcClient implements DiscoveryListener{
   
    //object used for waiting
    private static Object lock=new Object();
   
    //vector containing the devices discovered
    public static Vector vecDevices = new Vector();
   
    private static String connectionURL=null;
    //private static ServiceRecord serviceRecord = null;
    //private static Vector services;
    
    private static PcClient client = new PcClient();
    private static LocalDevice localDevice;
    private static DiscoveryAgent agent;
	
	static Date lastRun = null;
	static boolean isTransmitted = false;
	
	private static BafDecoder bafDecoder = new BafDecoder();
	
    //*********************************Wocket Commands***************************************************************
    public final static byte[] WOCKET_60_SEC_BURST_PACKET = {(byte) 0xBA, (byte)0x20};
    public final static byte[] WOCKET_Continuous_PACKET = {(byte) 0xBA, (byte)0x00};
    public final static byte[] WOCKET_GET_WTM_PACKET = {(byte) 0xBE};
    public final static byte[] WOCKET_GET_BATTERY_LEVEL = {(byte) 0xA0};
    public final static byte[] WOCKET_BATTERY_CALIBRATION_PACKET = {(byte) 0xB5, 0,0,0,0,0,0,0,0,0};
    public final static byte[] WOCKET_SET_LED_PACKET = {(byte) 0xBC, (byte)0x02}; //Yellow_ LED on for 2 Seconds    
    public final static byte[] WOCKET_SET_TCT_PACKET = {(byte) 0xB9, (byte)0x1E, (byte) 0x80, (byte)0x1F, (byte)0x70};
    //****************************************************************************************************************
    
    //****************************Find Devices***********************************
    public static void findDevices()throws IOException {
    	
        //display local device address and name
        localDevice = LocalDevice.getLocalDevice();
        System.out.println("Address: "+localDevice.getBluetoothAddress());
        System.out.println("Name: "+localDevice.getFriendlyName());   
        
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
               
        //print all devices in vecDevices
        int deviceCount=vecDevices.size();
       
        if(deviceCount <= 0){
            System.out.println("No Devices Found .");
            System.exit(0);
        }        
    }
    
    //****************************Connect****************************************
    public static StreamConnection connect(RemoteDevice remoteDevice)throws IOException{
        //check for spp service
        
        UUID[] uuidSet = new UUID[1];
        uuidSet[0]=new UUID("1101",true);
        int[] attrSet={0x1101}; // Sending this parameter is necessary for connecting to Wockets
        StreamConnection streamConnection = null;
        
        //System.out.println("\nSearching for service...");       
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
        try{
        //connect to the Wocket (as the server) 
        	streamConnection=(StreamConnection)Connector.open(connectionURL);
        }catch (BluetoothConnectionException e) {
        	e.printStackTrace();
        	System.out.println("Not responding");
    	}
        
        return streamConnection;
    }    
    
  //****************************Main*******************************************
    public static void main(String[] args) throws IOException, InterruptedException {    	
    	
    	
    	//----------------------Calling BafDecoder ----------------------------
    	/*SimpleDateFormat dayFormat = new SimpleDateFormat("yyyy-MM-dd HH:mm");
    	Date startDate=null, endDate=null;
		
			try {
				startDate = dayFormat.parse("2012-08-08 16:00");
				endDate = dayFormat.parse("2012-08-08 18:00");
			} catch (ParseException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}			
		
    	bafDecoder.decodeAndSaveDataWithStream( startDate, endDate,  ID);*/
    	//---------------------------------------------------------------------
    	findDevices();
    	
    	System.out.println("Bluetooth Devices: " + vecDevices.size());
    	int btSize = vecDevices.size();
    	for (int i = 0; i < btSize; i++) {
        	RemoteDevice remoteDevice=(RemoteDevice)vecDevices.elementAt(i);
        	String adr= remoteDevice.getBluetoothAddress();            
            if (adr.contains("0006660")){
            	System.out.println((i+1)+". "+ "Wocket-"+adr.substring(8) + " "+ remoteDevice.getBluetoothAddress());
            }else{
                vecDevices.removeElementAt(i);
                i--;
                btSize--;
            }
        }

        System.out.print("Choose Device indices separated with a space: ");
        
        BufferedReader bReader=new BufferedReader(new InputStreamReader(System.in));    
    	String chosenIndeces=bReader.readLine();
    	String[] ind = chosenIndeces.split(" ");
    	int num = ind.length;
		int[] indeces = new int[num];
		RemoteDevice[] remoteDevice =  new RemoteDevice[num]; 
		for (int j=0; j <num; j++){
			indeces[j] = Integer.parseInt(ind[j]) - 1;
			remoteDevice[j] = (RemoteDevice)vecDevices.elementAt(indeces[j]);
		}
    	//collectData(remoteDevice);
    	
    }//main     
    
    //****************************collecting Data******************************
    public static void collectData(RemoteDevice[] remoteDevice, JTextArea textArea) throws IOException, InterruptedException{
    	
    	WocketParam wocketParam = new WocketParam();
        int MAX_SIZE = 20000;
        byte[] wocketData = new byte[MAX_SIZE];
        boolean decodeFlag = false;
        int tail = 0;
        WocketDecoder myDecoder = new WocketDecoder();
        
    	int numberReadBytes = 0;
    	int num = remoteDevice.length;   	
		int[] seqNum = new int[num];    
		
		for (int j=0; j <num; j++){
			seqNum[j] = -1;
		}
	    
	    StreamConnection streamConnection;
	    OutputStream outStream; 
		InputStream inStream;
	  	       
	    while (true){  
	    	Date date = Calendar.getInstance().getTime();
	    	compressANDTransferZipFiles(date);
	    	for (int cnt=0; cnt<num; cnt++){
	        	streamConnection = connect(remoteDevice[cnt]);        	
	        	if (streamConnection == null){
	        		 System.out.println("not connected");
                     textArea.append("not connected\n");
                     textArea.validate();
                     beepRunnable.run();
	                 BlueCoveImpl.shutdown();	                              
	        		 continue;
	        	}
	        	String ID = remoteDevice[cnt].getBluetoothAddress();
	            System.out.println("Connect to Wocket-" + ID.substring(8));
                textArea.append("Connect to Wocket-" + ID.substring(8) + "\n");
                //textArea.validate();
                textArea.update(textArea.getGraphics());
	            outStream = streamConnection.openOutputStream();
	            inStream = streamConnection.openInputStream();

	            outStream.write(WOCKET_60_SEC_BURST_PACKET);
	            outStream.write(WOCKET_60_SEC_BURST_PACKET);
	            /*try {
	    			Thread.sleep(200);
	    		} catch (InterruptedException e) {
	    			e.printStackTrace();
	    		}
	            outStream.write(WOCKET_60_SEC_BURST_PACKET);
	            outStream.write(WOCKET_60_SEC_BURST_PACKET);
	            
	            outStream.write(WOCKET_SET_LED_PACKET[0]);
	        	try {
	    			Thread.sleep(200);
	    		} catch (InterruptedException e) {
	    			e.printStackTrace();
	    		}
	        	outStream.write(WOCKET_SET_LED_PACKET[1]);
	        	*/
	        	/*try {
	    			Thread.sleep(1000);
	    		} catch (InterruptedException e) {
	    			e.printStackTrace();
	    		} */
	
	            //--------------send an ack----------------------
	            byte[]_Bytes = new byte[4];
				int param = seqNum[cnt];
				byte temp = (byte)(param >> 8); 
				_Bytes[0] = (byte)0xBB;
				_Bytes[1] = (byte)((byte)(temp >>> 1) & 0x7f);
				_Bytes[2] = (byte)((byte)(temp << 6) & 0x40);
				temp = (byte)(param);
				_Bytes[2] |= (byte)((byte)(temp >> 2) & 0x3f);
				_Bytes[3] = (byte) ((byte)(temp << 5) & 0x60);
				for (int m=0; m<_Bytes.length; m++){
					outStream.write(_Bytes[m]);
					//outStream.flush();
					try {
					Thread.sleep(200);
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
				//outStream.flush();
				System.out.println("sends an ack with seqNum: "+ seqNum[cnt]);
				//-------------------------------------------------
				
	            numberReadBytes = 0;
	            byte[] data = {(byte) -1};
	            while (data[0] == -1)  { //to pass the 0xff bytes the Wocket sends
	            	data[0] = (byte) inStream.read();
	            }
	            while (data[0] != -46){  //end of a batch
	            	if (data[0] != -1){ // to check if input stream is available;  If no byte is available because the stream is at the end of the file, the value -1 is returned for inStream.read();	            		
		    			wocketData[tail] =(byte) data[0];
		    			tail ++;
		    			numberReadBytes ++;
		    			decodeFlag = true;
		    			if (tail == (MAX_SIZE))
		    				tail = 0;
	            	} else
	            		break;
	            	data[0] =(byte) inStream.read();
	    		}
	            
	            if (decodeFlag == true){
	    	    	 
	            	myDecoder.Decode(wocketData, tail, wocketParam, ID , seqNum[cnt], textArea);
	    	    	decodeFlag = false;
	    	    	System.out.println("decode " + wocketParam.uncompressedCount + " uncompressed raw packets and " + wocketParam.compressedCount + " compressed raw packets");
                    textArea.append("received " + ( wocketParam.uncompressedCount + wocketParam.compressedCount) + " raw data packets\n");
                    textArea.update(textArea.getGraphics());
	    	    	seqNum[cnt] = (int)wocketParam.last_seqNumber;
	        	}
	            BlueCoveImpl.shutdown();
	            System.out.println("disconnect\n");	
                textArea.append("\n");
                textArea.update(textArea.getGraphics());
	    	}//for
	    	Thread.sleep(60000 - (num*10));
	    } 
    }
    
    
    //*********************************round***********************************    
    public static double round(double value, int places) {
        if (places < 0) throw new IllegalArgumentException();

        long factor = (long) Math.pow(10, places);
        value = value * factor;
        long tmp = Math.round(value);
        return (double) tmp / factor;
    }
    
    //******************************Stop***************************************
    public static void stop(){
        BlueCoveImpl.shutdown();
    }
    
    //******************************play sound*********************************
    public static final Runnable beepRunnable = new Runnable() {
        public void run() {                 
            try {
                java.applet.AudioClip clip = java.applet.Applet.newAudioClip(new java.net.URL("file:src/rsc/beep.wav"));
                clip.play();
            } catch (java.net.MalformedURLException murle) {
            System.out.println(murle);
            }
        }            
    };  

    //**********************Send BAF and AC data to the server************************        
	public static void compressANDTransferZipFiles(Date now){
		//reset configuration info in the beginning of a new day 
		
		if(lastRun == null){
			Calendar logDt = Calendar.getInstance();
	        lastRun = logDt.getTime();	
	        return;
		}
		RawDataFileHandler rawDataFileHandler = new RawDataFileHandler();
		SummaryDataFileHandler summaryDataFileHandler = new SummaryDataFileHandler(); 
		int hour = now.getHours();    		
		   		
		//transmit zip files to server after 10pm
		if(isTransmitted && hour < 17){
			isTransmitted = false;
		}
		else if(!isTransmitted && hour >= 17){
			
			rawDataFileHandler.zipRawData(lastRun);
			if(rawDataFileHandler.transmitRawData())
				isTransmitted = true;
			summaryDataFileHandler.zipRawData(lastRun);
			if(summaryDataFileHandler.transmitSummaryData())
				isTransmitted = true; 
		}
	}
    
    //******************************send file*********************************	
	  public static void sendFile (String fileName ) throws IOException {
		  File file = new File(fileName);
		  int filesize=(int)file.length(); // file size temporary hardcoded
	
	    long start = System.currentTimeMillis();
	    int bytesRead;
	    int current = 0;
	    String SERVER_ADDR = "http://wockets.ccs.neu.edu:8080/FileUploader/Commonsfileuploadservlet";
	    // localhost for testing
	    Socket sock = new Socket(SERVER_ADDR, 0);
	    System.out.println("Connecting...");
	
	    // receive file
	    byte [] mybytearray  = new byte [filesize];
	    InputStream is = sock.getInputStream();
	    FileOutputStream fos = new FileOutputStream(file);
	    BufferedOutputStream bos = new BufferedOutputStream(fos);
	    bytesRead = is.read(mybytearray,0,mybytearray.length);
	    current = bytesRead;
	    
	    do {
	       bytesRead =
	          is.read(mybytearray, current, (mybytearray.length-current));
	       if(bytesRead >= 0) current += bytesRead;
	    } while(bytesRead > -1);
	
	    bos.write(mybytearray, 0 , current);
	    bos.flush();
	    long end = System.currentTimeMillis();
	    System.out.println(end-start);
	    bos.close();
	    sock.close();
	  }
	  
    			
    //*********************methods of DiscoveryListener************************
    @Override
    public void deviceDiscovered(RemoteDevice btDevice, DeviceClass cod) {
    	
        //add the device to the vector
        if(!vecDevices.contains(btDevice)) {
            vecDevices.addElement(btDevice);            
        }
    }
    //*************************************************************************
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