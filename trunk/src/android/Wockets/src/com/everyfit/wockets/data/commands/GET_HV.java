/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class GET_HV extends Command {

	/**
	 * 
	 */
	public GET_HV() {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0};
		this._Bytes[0]|=(byte) CommandTypes.GET_HV.ordinal();
	}

}
