/**
 * 
 */
package com.everyfit.wockets.data.commands;

/**
 * @author albinali
 *
 */
public final class SET_TCT extends Command {

	/**
	 * 
	 */
	public SET_TCT(int tct,int reps,int last) {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0,0,0,0,0,0,0,0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_TCT.ordinal();
		this._Bytes[1]=(byte) ((byte)tct>>1);
		this._Bytes[2]=(byte) ((((byte)tct&0x01)<<6)|((byte)reps>>2));
		this._Bytes[3]=(byte) ((((byte)reps & 0x03)<<5) |  ((byte)last>>3));
		this._Bytes[4]=(byte) (((byte)last&0x07)<<4);
	}

}
