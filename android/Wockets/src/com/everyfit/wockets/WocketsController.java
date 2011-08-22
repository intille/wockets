package com.everyfit.wockets;


import java.util.Calendar;
import java.util.Hashtable;
import java.util.ArrayList;
import java.util.TimeZone;
import java.nio.channels.FileChannel;
import java.text.DecimalFormat;


import android.os.Environment;
import com.everyfit.wockets.utils.XMLSerializable;
import com.everyfit.wockets.utils.network.*;
import com.everyfit.wockets.data.types.TransmissionMode;
import com.everyfit.wockets.decoders.AndroidDecoder;
import com.everyfit.wockets.decoders.Decoder;
import com.everyfit.wockets.decoders.DecoderList;
import com.everyfit.wockets.decoders.WocketDecoder;
import com.everyfit.wockets.receivers.AndroidReceiver;
import com.everyfit.wockets.receivers.RFCOMMReceiver;
import com.everyfit.wockets.receivers.Receiver;
import com.everyfit.wockets.receivers.ReceiverList;
import com.everyfit.wockets.sensors.AndroidSensor;
import com.everyfit.wockets.sensors.SensorList;
import com.everyfit.wockets.sensors.Sensor;
import com.everyfit.wockets.sensors.Wocket;

//for creating xml
import org.xmlpull.v1.XmlPullParser;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import android.content.Intent;
import android.util.Log;
import android.util.Xml;


public class WocketsController  implements XMLSerializable{
	private final String TAG = "WocketsController";	
	public NetworkStacks _Network;
	public Hashtable<String,String> _SelectedWockets;
	public TransmissionMode _TransmissionMode;	
	public String _RootPath="";	
	public String _DataStoragePath="";
	private boolean running=true;	
	
	//Wockets Controller Components
	public SensorList _Sensors;
	public ReceiverList _Receivers;
	public DecoderList _Decoders;
	
	//String constants for xml serialization
	private static final String _RECEIVERS = "RECEIVERS";
	private static final String _RECEIVER = "RECEIVER";
	private static final String _DECODERS = "DECODERS";
	private static final String _DECODER = "DECODER";
	private static final String _SENSORS = "SENSORS";
	private static final String _SENSOR = "SENSOR";
	private static final String _TYPE = "type";
	private static final String _RFCOMM = "RFCOMM";
	private static final String _ID = "id";
	private static final String _MAC = "MacAddress";
	private static final String _ANDROID = "Android";
	private static final String _MAXSR = "MaxSR";
	private static final String _WOCKETS = "Wockets";
	private static final String _CLASS = "class";
	private static final String _SR = "SR";
	private static final String _TEXT = "text";
	private static final String _LOCATION = "LOCATION";
	
	
	public WocketsController(){	
		//Need to add support for other media
		this._RootPath=Environment.getExternalStorageDirectory().getAbsolutePath()+"/wockets/";		
		DecimalFormat twoPlaces = new DecimalFormat("00");
	    Calendar now = Calendar.getInstance();
	    now.setTimeInMillis(System.currentTimeMillis());
	    TimeZone tz = TimeZone.getDefault();
	    long offset = tz.getOffset(now.getTimeInMillis());
	    long ms = now.getTimeInMillis() + offset;
	    Calendar newnow = Calendar.getInstance();
	    newnow.setTimeInMillis(ms);
	    this._DataStoragePath=this._RootPath+"Session-" + (twoPlaces.format(now.get(Calendar.MONTH) + 1)) + "-" + twoPlaces.format(now.get(Calendar.DAY_OF_MONTH)) + "-" + now.get(Calendar.YEAR) + "-" + twoPlaces.format(now.get(Calendar.HOUR_OF_DAY)) + "-" + twoPlaces.format(now.get(Calendar.MINUTE)) + "-" + twoPlaces.format(now.get(Calendar.SECOND))+"/";
	}
		
	public void Initialize() {		
		this._TransmissionMode=TransmissionMode.Continuous;
		_Network=new NetworkStacks();
		_Network.Initialize();			
		this._Receivers = new ReceiverList();
		this._Decoders = new DecoderList();
		this._Sensors = new SensorList();
	}

	public void Discover(){
		NetworkStacks._BluetoothStack.Discover();
	}
	public void Connect(ArrayList<String> wockets)
	{
			
		//copying SensorData.xml to data folder
		String srcSensorData = Environment.getExternalStorageDirectory().getAbsolutePath() + "/wockets/SensorData.xml";
		String destSensorData = this._DataStoragePath + "SensorData.xml";
		copyFile(srcSensorData, destSensorData);
		
		Intent intent = new Intent();
		intent.setClassName("com.everyfit.wockets.apps", "com.everyfit.wockets.apps.CollectDataService");
		WocketsService._Context.startService(intent);
		
		//this.start();		
	}
	
	public int getSensorId(String address)
	{
		ArrayList<Hashtable<String,String>> arrRecievers = new ArrayList<Hashtable<String,String>>();
		int id = -1;
		try
        {
        	XmlPullParser parser = Xml.newPullParser();        	           
            FileInputStream sensordatastream = new FileInputStream(Environment.getExternalStorageDirectory().getAbsolutePath() + "/wockets/SensorData.xml");
            parser.setInput(sensordatastream,null);
            Boolean done = false;                       
            Boolean receiver = false;
            
            int eventType = parser.getEventType();
            while(eventType != XmlPullParser.END_DOCUMENT && !done)
            {            	
            	String name = null;                     	
            	switch(eventType)
            	{
            		case XmlPullParser.START_TAG :
            		{
            			name = parser.getName();
            			if(name.equalsIgnoreCase("RECEIVERS"))
            			{
            				receiver = true;
            			}
            			if(name.equalsIgnoreCase("RECEIVER"))
            			{
            				if(receiver)
            				{
            					Hashtable<String,String> hshReciever = new Hashtable<String,String>();
                				for(int i = 0 ; i < parser.getAttributeCount();i++)
                				{
                					hshReciever.put(parser.getAttributeName(i), parser.getAttributeValue(i));
                				}
                				arrRecievers.add(hshReciever);
            				}
            				
            			}            			
            		}
            		case XmlPullParser.END_TAG :
            		{
            			name = parser.getName();
            			
            			if(name.equalsIgnoreCase("RECEIVERS"))
            			{
            				receiver = false;
            			}
            			break;
            		}
            			            			
            		case XmlPullParser.END_DOCUMENT :
            		{
            			done = true;
            			break;
            		}            			            		            	
            	}
            	eventType = parser.next();
            }            
        }
        catch(Exception ex)
        {
        	Log.e(TAG, "Unable to get Sensor Id");
        	        
        }
        
        for(int i = 0 ; i < arrRecievers.size() ; i ++)
        {
        	Hashtable<String,String> hshReciever = arrRecievers.get(i);
        	if(hshReciever.get("MacAddress").equalsIgnoreCase(address))
        		id =  Integer.parseInt(hshReciever.get("id"));
        }
        return id;

	}
	
	public void copyFile(String src, String dest)
	{
		FileChannel in = null;
		FileChannel out = null;
		File sensorData = new File(dest);
		
		try
		{
			File dir = new File(sensorData.getParent());
			if(! dir.isDirectory())
				dir.mkdirs();			
			in = new FileInputStream(src).getChannel();
			out = new FileOutputStream(sensorData).getChannel();
			
			out.transferFrom(in, 0, in.size());
			
			if(in != null)
				in.close();
			if(out != null)
				out.close();
		}
		catch(Exception ex)
		{
			System.out.println(ex.getMessage());
		}		
	}
	
	public void Disconnect(){
		for(Sensor sensor:this._Sensors)
			sensor.Dispose();
		//this.stop();
	}
	
	public void Dispose(){
		running=false;		
				
		if (this._Sensors!=null){
			for(Sensor sensor:this._Sensors)
			{				
				sensor._Decoder.Dispose();
				sensor._Receiver.Dispose();
			}
		}
		
		_Network.Dispose();
	}

	public String ToXML() 
	{
		return "";
	}

	public void FromXML(String xml) 
	{
		try
		{
			XmlPullParser parser = Xml.newPullParser();
			FileInputStream sensorDataXml = new FileInputStream(xml);
			parser.setInput(sensorDataXml,null);
            boolean done = false;
            boolean receivers = false;
            boolean decoders = false;  
            boolean sensors = false;
            String receiverType = null;
            String decoderType = null;
            String sensorType = null;
            
            Hashtable<String,String> hshTemp; 
            Receiver receiver;           
            Decoder decoder;
            Sensor sensor;
            
            int eventType  = parser.getEventType();
            while(eventType != XmlPullParser.END_DOCUMENT && !done)
            {
            	String name = null;
            	switch(eventType)
            	{
	            	case XmlPullParser.START_TAG :
	            	{
	            		name = parser.getName();
	            		
	            		if(name.equalsIgnoreCase(WocketsController._RECEIVERS))
	            		{
	            			receivers = true;
	            		}
	            		else if(name.equalsIgnoreCase(WocketsController._RECEIVER))
	            		{
	            			if(receivers)
	            			{
	            				hshTemp = new Hashtable<String,String>();
		            			for(int i = 0 ; i < parser.getAttributeCount(); i++)
		            			{
		            				hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
		            			}
		            			
	            				receiverType = hshTemp.get(WocketsController._TYPE);
	            				if(receiverType.equalsIgnoreCase(WocketsController._RFCOMM))
	            				{
	            					receiver = new RFCOMMReceiver(Integer.parseInt(hshTemp.get(WocketsController._ID)),
	            							hshTemp.get(WocketsController._MAC));
	            					receiver._maxSR = Integer.parseInt(hshTemp.get(WocketsController._MAXSR));
	            					this._Receivers.add(receiver);
	            				}
	            				else if(receiverType.equalsIgnoreCase(WocketsController._ANDROID))
	            				{
	            					receiver = new AndroidReceiver(Integer.parseInt(hshTemp.get(WocketsController._ID)));
	            					receiver._maxSR = Integer.parseInt(hshTemp.get(WocketsController._MAXSR));
	            					this._Receivers.add(receiver);
	            				}	            					            			
	            			}	            			
	            		}
	            		else if(name.equalsIgnoreCase(WocketsController._DECODERS))
	            		{
	            			decoders = true;
	            		}
	            		else if(name.equalsIgnoreCase(WocketsController._DECODER))
	            		{
	            			if(decoders)
	            			{
	            				hshTemp = new Hashtable<String, String>();
	            				for(int i = 0 ; i < parser.getAttributeCount(); i++)
		            			{
		            				hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
		            			}
	            				
            					decoderType = hshTemp.get(WocketsController._TYPE);
            					if(decoderType.equalsIgnoreCase(WocketsController._WOCKETS))
            					{
            						decoder = new WocketDecoder(Integer.parseInt(hshTemp.get(WocketsController._ID)));
            						this._Decoders.add(decoder);
            					}
            					else if(decoderType.equalsIgnoreCase(WocketsController._ANDROID))
            					{
            						decoder = new AndroidDecoder(Integer.parseInt(hshTemp.get(WocketsController._ID)));
            						this._Decoders.add(decoder);
            					}	            				
	            			}
	            		}
	            		else if(name.equalsIgnoreCase(WocketsController._SENSORS))
	            		{
	            			sensors = true;
	            		}
	            		else if(name.equalsIgnoreCase(WocketsController._SENSOR))
	            		{	            				            		
	            			if(sensors)
	            			{
	            				int id = 0;
		            			int sr;
		            			int recID;
		            			int decID;
		            			String address = null;
		            			String location;
		            			
	            				hshTemp = new Hashtable<String, String>();
	            				for(int i = 0 ; i < parser.getAttributeCount(); i++)
	            				{
	            					hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));	            					
	            				}
	            				sensorType = hshTemp.get(WocketsController._CLASS);
	            				
	            				int subEventType = parser.next();
            					String subName;
            					boolean flag = true;
            					while (flag)
            					{
            						
            						switch(subEventType)
            						{
            							case XmlPullParser.START_TAG :
            							{
            								subName = parser.getName();
            								
            								if(subName.equalsIgnoreCase(WocketsController._ID.toUpperCase()))
            								{
            									hshTemp = new Hashtable<String, String>();
            									for(int i = 0 ; i < parser.getAttributeCount(); i++)
            										hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
            									id = Integer.parseInt(hshTemp.get(WocketsController._ID));
            								}
            								else if (subName.equalsIgnoreCase(WocketsController._SR))
            								{
            									hshTemp = new Hashtable<String, String>();
            									for(int i = 0 ; i < parser.getAttributeCount(); i++)
            										hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
            									sr = Integer.parseInt(hshTemp.get(WocketsController._TEXT));
            								}
            								else if(subName.equalsIgnoreCase(WocketsController._RECEIVER))
            								{
            									hshTemp = new Hashtable<String, String>();
            									for(int i = 0 ; i < parser.getAttributeCount(); i++)
            										hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
            									recID = Integer.parseInt(hshTemp.get(WocketsController._ID));
            								}
            								else if(subName.equalsIgnoreCase(WocketsController._DECODER))
            								{
            									hshTemp = new Hashtable<String, String>();
            									for(int i = 0 ; i < parser.getAttributeCount(); i++)
            										hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
            									decID = Integer.parseInt(hshTemp.get(WocketsController._ID));
            								}
            								else if(subName.equalsIgnoreCase(WocketsController._LOCATION))
            								{
            									hshTemp = new Hashtable<String, String>();
            									for(int i = 0 ; i < parser.getAttributeCount(); i++)
            										hshTemp.put(parser.getAttributeName(i), parser.getAttributeValue(i));
            									location = hshTemp.get(WocketsController._TEXT);
            								}
            							}
            							case XmlPullParser.END_TAG :
            							{
            								subName = parser.getName();
            								if (subName.equalsIgnoreCase(WocketsController._SENSOR))
            								{
            									flag = false;
            									break;
            								}
            							}
            						}
            						subEventType = parser.next();
            					}
	            				
	            				if(sensorType.equalsIgnoreCase(WocketsController._WOCKETS))
	            				{
	            					for(int i = 0 ; i < this._Receivers.size(); i++)
	            					{
	            						if(this._Receivers.get(i)._ID == id)
	            						{
	            							RFCOMMReceiver rfcom = (RFCOMMReceiver)this._Receivers.get(i);
	            							address = rfcom._Address;
	            						}
	            					}
	            					sensor = new Wocket(id,formatMacAddr(address),this._DataStoragePath);
	            					this._Sensors.add(sensor);
	            					
	            				}
	            				else if(sensorType.equalsIgnoreCase(WocketsController._ANDROID))
	            				{
	            					sensor = new AndroidSensor(id,this._DataStoragePath);
	            					this._Sensors.add(sensor);
	            				}
	            			}
	            		}
	            	}
	            	case XmlPullParser.END_TAG:
	            	{
//	            		name = parser.getName();
//	            		
//	            		if(name.equalsIgnoreCase(WocketsController._RECEIVERS))
//	            			receivers = false;
//	            		else if(name.equalsIgnoreCase(WocketsController._DECODERS))
//	            			decoders = false;
//	            		else if(name.equalsIgnoreCase(WocketsController._SENSORS))
//	            			sensors = false;
	            	}
            	}
            	eventType = parser.next();
            }
            
		}
		catch(Exception ex)
		{
			Log.e(TAG, "Error while loading wockets controller from xml");
		}
	}
	
	public String formatMacAddr(String addr)
	  {
		  String address = "";
		  if(addr.length()  == 12)
		  {
			  for(int i = 0 ; i < addr.length(); i++)
			  {
				  if(i == 0)
				  {
					  address += addr.charAt(i);
				  }
				  else if
				  ((i % 2 != 0) && (i != addr.length() -1))
				  {
					  address += addr.charAt(i) + ":"; 
				  }
				  else
				  {
					  address += addr.charAt(i);
				  }
			  }  
		  }		  
		  return address;
	  }
	
}
