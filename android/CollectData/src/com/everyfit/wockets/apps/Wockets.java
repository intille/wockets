package com.everyfit.wockets.apps;



import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

import android.content.SharedPreferences;



/**
 * @author albinali
 *
 */
public class Wockets extends ArrayList<Wocket> {

	

	public ArrayList<String> toAddressArrayList(){
		ArrayList<String> addresses=new ArrayList<String>();
		for (Wocket wocket:this)
			addresses.add(wocket._Address);
		return addresses;
	}
	public String[] toAddressArray(){
		String[] addresses=new String[this.size()];
		int index=0;
		for (Wocket wocket:this)
			addresses[index++]=wocket._Address;
		return addresses;
	}
	
	public int[] toPlacementArray(){
		int[] placements=new int[this.size()];
		int index=0;
		for (Wocket wocket:this)
			placements[index++]=wocket._Placement;
		return placements;
	}
	
	
}
