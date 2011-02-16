/**
 * 
 */
package com.everyfit.wockets.receivers;

import java.util.ArrayList;

/**
 * @author albinali
 *
 */
public final class ReceiverList extends ArrayList<Receiver> {

	public ReceiverList(){
		
	}
	
	public void Dispose(){
		for (Receiver r:this)
			r.Dispose();
	}
}
