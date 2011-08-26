/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author Fahd Albinali
 *
 */
public final class ACK extends Command {

	/**
	 * 
	 */
	public ACK() {
		// TODO Auto-generated constructor stub		
		this._Bytes = new byte[] { (byte)0xa0};
		this._Bytes[0]|=(byte) CommandTypes.ACK.ordinal();
	}

}
