/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class PAUSE extends Command {

	/**
	 * 
	 */
	public PAUSE() {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0};
		this._Bytes[0]|=(byte) CommandTypes.PAUSE.ordinal();
	}

}
