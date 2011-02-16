/**
 * 
 */
package com.everyfit.wockets.data.commands;

import com.everyfit.wockets.data.types.TransmissionMode;

/**
 * @author albinali
 *
 */
public final class SET_VTM extends Command {

	/**
	 * 
	 */
	public SET_VTM(TransmissionMode mode) {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_VTM.ordinal();
		this._Bytes[1]=(byte)(((byte)mode.ordinal()) << 4);
	}

}
