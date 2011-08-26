/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class RST_WKT extends Command {

	/**
	 * 
	 */
	public RST_WKT() {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0};
		this._Bytes[0]|=(byte) CommandTypes.RST_WKT.ordinal();
	}

}
