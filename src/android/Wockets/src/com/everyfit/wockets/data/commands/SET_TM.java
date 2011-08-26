/**
 * 
 */
package com.everyfit.wockets.data.commands;

import com.everyfit.wockets.data.types.TransmissionMode;
/**
 * @author albinali
 *
 */
public final class SET_TM extends Command {

	/**
	 * 
	 */
	public SET_TM(TransmissionMode mode) {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_TM.ordinal();
		this._Bytes[1]=(byte)(((byte)mode.ordinal()) << 4);
	}

}
