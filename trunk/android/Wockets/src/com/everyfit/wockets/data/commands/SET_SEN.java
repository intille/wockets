/**
 * 
 */
package com.everyfit.wockets.data.commands;

import com.everyfit.wockets.data.types.Sensitivity;
/**
 * @author albinali
 *
 */
public final class SET_SEN extends Command {

	/**
	 *           
	 */
	public SET_SEN(Sensitivity sensitivity) {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_SEN.ordinal();
		this._Bytes[1]=(byte) (((byte)sensitivity.ordinal())<<3);
	}

}
