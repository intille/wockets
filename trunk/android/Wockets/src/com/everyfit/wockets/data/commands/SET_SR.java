/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class SET_SR extends Command{

	/**
	 */
	public SET_SR(int sr) {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_SR.ordinal();
		this._Bytes[1]=(byte) (sr&0x7f);
	}

}
