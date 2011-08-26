/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class SET_PDT extends Command {

	/**
	 */
	public SET_PDT(int timeout) {		
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_PDT.ordinal();
		this._Bytes[1]=(byte) (timeout&0x7f);
	}

}
