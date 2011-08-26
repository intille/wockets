/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class GET_TM extends Command {

	/**
	 * 
	 */
	public GET_TM() {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0};
		this._Bytes[0]|=(byte) CommandTypes.GET_TM.ordinal();
	}

}
