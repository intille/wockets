/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author Fahd Albinali
 *
 */
public final class ALIVE extends Command {

	/**
	 * 
	 */
	public ALIVE() {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0};
		this._Bytes[0]|=(byte) CommandTypes.ALIVE.ordinal();
	}

}
