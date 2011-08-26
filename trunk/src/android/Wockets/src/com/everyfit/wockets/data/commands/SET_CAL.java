/**
 * 
 */
package com.everyfit.wockets.data.commands;

import com.everyfit.wockets.data.types.Calibration;
/**
 * @author albinali
 *
 */
public final class SET_CAL extends Command {

	/**
	 *               
	 */
	public SET_CAL(Calibration cal) {
		// TODO Auto-generated constructor stub
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0,0,0,0,0,0,0,0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_CAL.ordinal();
		this._Bytes[1]=(byte) (cal._X1G>>3);
		this._Bytes[2]=(byte) (((cal._X1G&0x07)<<4)|(cal._XN1G>>6));
		this._Bytes[3]=(byte) (((cal._XN1G & 0x3f)<<1) |  (cal._Y1G>>9));
		this._Bytes[4]=(byte) ((cal._Y1G>>2) & 0x7f);
		this._Bytes[5]=(byte) (((cal._Y1G&0x03)<<5)| (cal._YN1G>>5));
		this._Bytes[6]=(byte) (((cal._YN1G&0x1f)<<2)| (cal._Z1G>>8));
		this._Bytes[7]=(byte) ((cal._Z1G>>1)&0x7f);
		this._Bytes[8]=(byte) (((cal._Z1G&0x01)<<6)|(cal._ZN1G>>4));
		this._Bytes[9]=(byte) ((cal._ZN1G&0x0f)<<3);
	}

}
