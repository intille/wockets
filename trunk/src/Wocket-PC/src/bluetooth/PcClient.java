
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
import UserInterface.SetSamplingRate;
import com.intel.bluetooth.BlueCoveImpl;
import java.io.*;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.bluetooth.*;
import javax.swing.JLabel;
import javax.swing.JTextArea;


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
    
    
    //*********************************Wocket Commands***************************************************************
    public final static byte[] WOCKET_60_SEC_BURST_PACKET = {(byte) 0xBA, (byte)0x20};
    public final static byte[] WOCKET_Continuous_PACKET = {(byte) 0xBA, (byte)0x00};
    public final static byte[] WOCKET_GET_WTM_PACKET = {(byte) 0xBE};
    public final static byte[] WOCKET_GET_BATTERY_LEVEL = {(byte) 0xA0};
    public final static byte[] WOCKET_BATTERY_CALIBRATION_PACKET = {(byte) 0xB5, 0,0,0,0,0,0,0,0,0};
    public final static byte[] WOCKET_SET_LED_PACKET = {(byte) 0xBC, (byte)0x02}; //Yellow_ LED on for 4 Seconds    
    public final static byte[] WOCKET_SET_TCT_PACKET = {(byte) 0xB9, (byte)0x1E, (byte) 0x80, (byte)0x1F, (byte)0x70};
    //****************************************************************************************************************
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
    public static void Calibrate_SamplingRate(double fav_samplingRate, InputStream inStream, OutputStream outStream, JLabel textArea) throws IOException{
    	byte tct, reps, last;
    	double ticks = (int)(7812/fav_samplingRate);//8MHz/2^10=7812
    	double accuracy;
    	double samplingRate = measureSamplingRate(inStream, 2, textArea );
        double diff = samplingRate - fav_samplingRate;
        if (diff < 0){
        	accuracy= (7812/(ticks-1))-fav_samplingRate;        	
        }  else{
        	accuracy= fav_samplingRate-(7812/(ticks+1));
        }
        System.out.println("Accuracy of calobrating Sampling rate: +/-("+round(accuracy,2)+")");
        if (Math.abs(diff) < accuracy){
            System.out.println("The Wocket is already calibrated: "+samplingRate);
            return;
    	}
        System.out.println("Start calibration...");
        System.out.println("The sampling rate before calibration: "+samplingRate);
        System.out.println("Apply the default setting...");
        set_sr(ticks, outStream);     	
    	samplingRate = measureSamplingRate(inStream, 2, textArea );
    	double tick1 = ticks;
    	while (Math.abs(diff)> accuracy){
	    	double tick2 = tick1*samplingRate/fav_samplingRate;
	    	if (Math.abs( tick2 - Math.floor(tick2) ) < 0.5)
	    		tick2 = Math.floor(tick2);
	    	else 
	    		tick2 = Math.ceil(tick2);
	    	if (tick2 != tick1){	
	    		System.out.println("Modify the sampling rate...");
		    	set_sr(tick2, outStream);		    	
		    	samplingRate = measureSamplingRate(inStream, 2, textArea );
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
	public static double measureSamplingRate(InputStream inStream, int t, JLabel textArea)throws IOException{
            JLabel label = textArea;
            label.setText("Measuring the Wocket's sampling rate...");
            //jTextArea.invalidate();
            label.repaint();
	    System.out.println("Measuring the Wocket's sampling rate...");
	    WocketParam sr = new WocketParam();
	    int cnt = 7;
	    byte[] wocketData = new byte[cnt]; 
	    WocketDecoder myDecoder = new WocketDecoder(0);
	    while (sr.flag < t){
	            if (sr.total_time >= 60000){
	                    System.out.print("minute:"+(sr.flag+1));
	                    System.out.println("\tSampling Rate: "+ sr.samplingRate);
                            label.setText("minute:"+(sr.flag+1)+"\tSampling Rate: "+ sr.samplingRate);
                            //jTextArea.invalidate();
                            label.repaint();
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
            String msg = Double.toString(sr.samplingRate);
            log (msg);
	    return sr.samplingRate;
	}
	
    //******************************Test Battery****************************************    
    public static int[] testBattery(OutputStream outStream, InputStream inStream)throws IOException{
        System.out.println("Testing Wocket's battry...");
        ArrayList<Integer> battery = new ArrayList<Integer>();
        WocketParam sr = new WocketParam();
        int cnt = 7;
        byte[] wocketData = new byte[cnt]; 
        WocketDecoder myDecoder = new WocketDecoder(0);
        int minute = 0;
        long idleTime = 0;
        
        Calendar logDt = Calendar.getInstance();
        Date prev_time = logDt.getTime();
        Date current_time;
        long diff;
        while (idleTime < 30000){
            /*if (sr.total_time >= 59950){
                outStream.write(WOCKET_GET_BATTERY_LEVEL);outStream.flush();
            }*/
            if (sr.total_time >= 60000){ //one minute                   
                outStream.write(WOCKET_GET_BATTERY_LEVEL);outStream.flush();
                System.out.println("minute:"+(minute+1)+"\tBattery: " +sr.battery);
                battery.add(sr.battery);
                String msg = Integer.toString(sr.battery);
                log (msg);
                sr.counter = 0;
                sr.total_time = 0;
                minute ++;  
                outStream.write(WOCKET_GET_BATTERY_LEVEL);outStream.flush();                
            }
            logDt = Calendar.getInstance();
            current_time = logDt.getTime();            
            diff = current_time.getTime() - prev_time.getTime();
            idleTime += diff;
            prev_time = current_time;
            if (inStream.available() > 0){
                    inStream.read(wocketData);
                    myDecoder.Decode(0, wocketData, cnt, sr); 
                    idleTime = 0;
            }
        } 
        
        
        int life = battery.size();
        int[] batterCalibrationValues = new int[6];
        double temp = 0;
        int index = 0;
        batterCalibrationValues[0] = Math.max(battery.get(index), battery.get(index+1)); //100%
        index = (int)(0.2*life); 
        batterCalibrationValues[1] =  Math.max(battery.get(index), battery.get(index+1));//80%
        index = (int)(0.4*life); 
        batterCalibrationValues[2] =  Math.max(battery.get(index), battery.get(index+1));//60%
        index = (int)(0.6*life);
        batterCalibrationValues[3] =  Math.max(battery.get(index), battery.get(index+1));//40%
        index = (int)(0.8*life);
        batterCalibrationValues[4] =  Math.max(battery.get(index), battery.get(index+1));//20%
        index = (int)(0.9*life);
        batterCalibrationValues[5] =  Math.max(battery.get(index), battery.get(index+1));//10%
        return batterCalibrationValues;
    }
	
	//*******************************Calibrate Battery**********************************************************************
    public static void CalibrateBattery(OutputStream outStream, int[] batteryCalibrationValues) throws IOException{
    	
    	int cal_100 = batteryCalibrationValues[0];
    	int cal_80  = batteryCalibrationValues[1];
    	int cal_60  = batteryCalibrationValues[2];
    	int cal_40  = batteryCalibrationValues[3];
    	int cal_20  = batteryCalibrationValues[4];
    	int cal_10  = batteryCalibrationValues[5];
    	
    	byte[] _Bytes = new byte[] {(byte) 0xB5, 0,0,0,0,0,0,0,0,0};
		_Bytes[1]=(byte)  ((cal_100 >> 3) & 0x7f);
		_Bytes[2]=(byte) (((cal_100 << 4) & 0x70) | ((cal_80  >> 6) & 0x0f));
		_Bytes[3]=(byte) (((cal_80  << 1) & 0x7e) | ((cal_60  >> 9) & 0x01));
		_Bytes[4]=(byte)  ((cal_60  >> 2) & 0x7f);
		_Bytes[5]=(byte) (((cal_60  << 5) & 0x60) | ((cal_40  >> 5) & 0x1f));
		_Bytes[6]=(byte) (((cal_40  << 2) & 0x7c) | ((cal_20  >> 8) & 0x03));
		_Bytes[7]=(byte)  ((cal_20  >> 1) & 0x7f);
		_Bytes[8]=(byte) (((cal_20  << 6) & 0x40) | ((cal_10  >> 4) & 0x3f));
    	_Bytes[9]=(byte)  ((cal_10  << 3) & 0x78);
    	
		for (byte b=0;b<2; b++){ // sending the command twice to be sure it is received by Wocket
			for (int m=0; m<10; m++){
				outStream.write(_Bytes[m]);
				outStream.flush();
				try {
				Thread.sleep(1000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
		}
    }
    
  //******************************test Axes**********************************************************
    public static int test_Axes(char axis, OutputStream outStream, InputStream inStream) throws IOException {
    	System.out.println("Testing Wocket's axes...");
	    WocketParam sr = new WocketParam();
	    int diff = 0;
	    int cnt = 7;
	    byte[] wocketData = new byte[cnt]; 
	    WocketDecoder myDecoder = new WocketDecoder(0);
	    while (sr.total_time <= 10000){ // 10 sec
            if (inStream.available() > 0){
                    inStream.read(wocketData);
                    myDecoder.Decode(0, wocketData, cnt, sr);    
            }
            if (sr.data_flag == 1){
            	sr.data_flag = 0;
            	switch(axis)
        		{
        			case 'x':
        				diff+= sr.x;
        				break;
        			case 'y':
        				diff+= sr.y;
        				break;
        			case 'z':
        				diff+= sr.z;
        				break;
        			default:
        				break;
        		}
            }
	    } 
	    
	    int mid_value = diff/ sr.counter;
            System.out.println("mid_value: "+mid_value);
	    return mid_value;
    }
    
  //******************************Measure Noise**********************************************************
    public static int measureNoise(OutputStream outStream, InputStream inStream, int mid_value) throws IOException {
    	System.out.println("Measuring Noise...");
	    WocketParam sr = new WocketParam();
	    int diff = 0;
	    int cnt = 7;
	    byte[] wocketData = new byte[cnt]; 
	    WocketDecoder myDecoder = new WocketDecoder(0);	    
	    while (sr.total_time <= 10000){ // 10 sec
            if (inStream.available() > 0){
                    inStream.read(wocketData);
                    myDecoder.Decode(0, wocketData, cnt, sr);    
            }
            if (sr.data_flag == 1){
            	sr.data_flag = 0;
            	diff= Math.abs(sr.x - mid_value);
            }
	    } 
	    int noise = diff / sr.counter;
            System.out.println("Noise: "+noise);
	    return noise;
    }
    
  //******************************Measure range**********************************************************
    public static int[] measure_range(char axis, OutputStream outStream, InputStream inStream) throws IOException {
    	System.out.println("Measuring accelerometer range...");
	    WocketParam sr = new WocketParam();
	    int max = 0;
	    int min = 1000;
	    int cnt = 7;
	    byte[] wocketData = new byte[cnt]; 
	    WocketDecoder myDecoder = new WocketDecoder(0);
	    while (sr.total_time <= 10000){ // 10 sec
            if (inStream.available() > 0){
                    inStream.read(wocketData);
                    myDecoder.Decode(0, wocketData, cnt, sr);    
            }
            if (sr.data_flag == 1){
            	sr.data_flag = 0;
            	switch(axis)
        		{
        			case 'x':
        				if (sr.x > max)
        					max = sr.x;
        				else if (sr.x < min)
        					min = sr.x;
        				break;
        			case 'y':
        				if (sr.y > max)
        					max = sr.y;
        				else if (sr.y < min)
        					min = sr.y;
        				break;
        			case 'z':
        				if (sr.z > max)
        					max = sr.z;
        				else if (sr.z < min)
        					min = sr.z;
        				break;
        			default:
        				break;
        		}
            }
	    }	    
	    System.out.println("min: "+min + "max: "+max);
	    return new int[]{max, min};
    }
    
    //******************************Calibrate Axes**********************************************************
    public static void calibrate_Accelerometer(OutputStream outStream, int cal_x, int cal_nx, int cal_y, 
    		int cal_ny, int cal_z, int cal_nz) throws IOException {
    	byte[] _Bytes = new byte[] {(byte) 0xB5, 0,0,0,0,0,0,0,0,0};
		_Bytes[1]=(byte)  ((cal_x >> 3) & 0x7f);
		_Bytes[2]=(byte) (((cal_x << 4) & 0x70) | ((cal_nx  >> 6) & 0x0f));
		_Bytes[3]=(byte) (((cal_nx  << 1) & 0x7e) | ((cal_y  >> 9) & 0x01));
		_Bytes[4]=(byte)  ((cal_y  >> 2) & 0x7f);
		_Bytes[5]=(byte) (((cal_y  << 5) & 0x60) | ((cal_ny  >> 5) & 0x1f));
		_Bytes[6]=(byte) (((cal_ny  << 2) & 0x7c) | ((cal_z  >> 8) & 0x03));
		_Bytes[7]=(byte)  ((cal_z  >> 1) & 0x7f);
		_Bytes[8]=(byte) (((cal_z  << 6) & 0x40) | ((cal_nz  >> 4) & 0x3f));
    	_Bytes[9]=(byte)  ((cal_nz  << 3) & 0x78);
    	
		for (byte b=0;b<2; b++){ // sending the command twice to be sure it is received by Wocket
			for (int m=0; m<10; m++){
				outStream.write(_Bytes[m]);
				outStream.flush();
				try {
				Thread.sleep(1000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
		}
    }
    
    //******************************log****************************************
    static Boolean flag= false; 
    private static SimpleDateFormat _DateFormat_log = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss.SSS");
    public static void log(String msg)
	{		
        Calendar logDt = Calendar.getInstance();
        logDt.setTimeInMillis(System.currentTimeMillis());
        Date logTmpDt = logDt.getTime();	

        File f = new File("samplingRate.csv");
        PrintWriter out = null;
        try {
                if (!(f.exists())) {
                        f.createNewFile();
                }
                if (!flag){
                        out = new PrintWriter(new FileWriter("samplingRate.csv"));
                        flag = true;
                } else
                        out = new PrintWriter(new FileWriter("samplingRate.csv",true));
        }
        catch (IOException e1) {
                e1.printStackTrace();
        }

        String s = _DateFormat_log.format(logTmpDt) + "," + msg + "\n";
        try {
                //out.println(s);
                out.append(s);
        }
        catch (NumberFormatException e) {
                System.out.println("Error while writing logs");
        }

        if (out != null) {
                out.close();
        }
	
	}
    
  //*********************************round****************************************    
    public static double round(double value, int places) {
        if (places < 0) throw new IllegalArgumentException();

        long factor = (long) Math.pow(10, places);
        value = value * factor;
        long tmp = Math.round(value);
        return (double) tmp / factor;
    }
    
    //******************************Stop****************************************
    public static void stop(){
        BlueCoveImpl.shutdown();
    }
    
    //******************************play sound****************************************
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