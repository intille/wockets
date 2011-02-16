package com.everyfit.wockets.apps;

import 	android.app.Activity;
import android.os.Bundle;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.widget.Button;
import android.widget.TextView;
import android.util.Log;
import android.view.View;
import com.everyfit.wockets.*;
import  com.everyfit.wockets.kernel.*;
import com.everyfit.wockets.utils.network.NetworkStacks;

import android.widget.ArrayAdapter;
import android.widget.ListView;
import android.widget.Toast;
import android.widget.TextView;
import java.util.Hashtable;

import java.util.HashMap;
import java.util.Enumeration;
import java.io.Serializable;
import android.widget.AdapterView.OnItemClickListener;
import android.widget.AdapterView;
import java.io.FileWriter;
import java.io.File;
import android.os.Environment;
import java.io.BufferedReader;
import java.io.FileReader;
import 	java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.FileOutputStream;

import android.net.wifi.WifiConfiguration;
import android.net.wifi.WifiInfo;
import android.net.wifi.WifiManager;
import android.net.wifi.ScanResult;
import android.content.BroadcastReceiver;
import java.util.ArrayList;

public class CollectData extends Activity implements KernelCallback {

	Button bWocketConnect;
	private static final String TAG = "ServicesDemo";
	private ListView lv1;
	private String[] wocketaddress;
	private Hashtable<String,String> selectedwockets;

		
	public void onCreate(Bundle savedInstanceState) {
	    super.onCreate(savedInstanceState);
	    setContentView(R.layout.main);    	

	    bWocketConnect = (Button) findViewById(R.id.connect);
	    bWocketConnect.setEnabled(true);
	    selectedwockets=new Hashtable<String,String>();
	   
        lv1=(ListView)findViewById(R.id.wlist);
        lv1.setChoiceMode(ListView.CHOICE_MODE_MULTIPLE);
        lv1.setOnItemClickListener(new OnItemClickListener() {
       	 	public void onItemClick(AdapterView<?> a, View v, int position, long id) {

       	 	       	 		
       	 		if (lv1.isItemChecked(position))
       	 			selectedwockets.put(((TextView) v).getText().toString(),((TextView) v).getText().toString());
       	 		else
       	 			selectedwockets.remove(((TextView) v).getText().toString());       	 		
       	 		
       	 		if (selectedwockets.isEmpty())
       	 			bWocketConnect.setEnabled(false);
       	 		else
       	 			bWocketConnect.setEnabled(true);       	 
       	 	}
       	 });
        
        KernelListener.callbacks.add(this);      
				
		Intent intent = new Intent(this, ApplicationListener.class);
		intent.putExtra("ApplicationMessage",ApplicationMessage.Ping.name());
		sendBroadcast(intent);
      
	}

	

	@Override
	protected void onPause() {
	    super.onPause();    
	}


	public void OnReceiveKernelMessage(Intent intent)
	{
		KernelMessage msg=KernelMessage.valueOf(intent.getExtras().getString("KernelMessage"));
		switch(msg){
			case Connected:
				Toast.makeText(this, "Wocket "+intent.getStringExtra("address")+" Connected", Toast.LENGTH_LONG).show();				
				break;
			case Disconnected:
				Toast.makeText(this, "Wocket "+intent.getStringExtra("address")+" disconnected", Toast.LENGTH_LONG).show();				
				break;						
			case Discovered:
				Toast.makeText(this, "Wockets discovery completed", Toast.LENGTH_LONG).show();
				Log.d(TAG, "Discovered");
				//bWocketDiscover.setEnabled(true);				
				Serializable data = intent.getSerializableExtra("table");
				if (data != null) {
					NetworkStacks._BluetoothStack._Discovered = new Hashtable<String, String>((HashMap<String, String>)data);
				}	
				Enumeration<String> e = NetworkStacks._BluetoothStack._Discovered.keys();
				wocketaddress=new String[ NetworkStacks._BluetoothStack._Discovered.size()];
				int i=0;
				while(e.hasMoreElements()){
					wocketaddress[i]=(String)e.nextElement();
					i++;
				}				 
				lv1.setAdapter(new ArrayAdapter<String>(this,android.R.layout.simple_list_item_multiple_choice , wocketaddress));
				break;				
		}		
	}
	
	  public void myClickHandler(View src) 
	  {
		  Intent intent;
		    switch (src.getId()) 
		    { 
		    	case R.id.connect:				    	
		    		if (Application._Context==null){
		    			Application._Context=this.getApplicationContext();
		    			Application._Wockets=new Wockets();
		    			Application._Wockets.add(new Wocket("00:06:66:05:23:81",0));
		    			Application._Wockets.add(new Wocket("00:06:66:03:E2:1B",1));
		    		}
		    		Intent i = new Intent();
		        	i.setClassName("com.everyfit.wockets.apps",
		                              "com.everyfit.wockets.apps.WocketsGraph");
		            startActivity(i);
		    		break;		    	
		    }
	  }
}
