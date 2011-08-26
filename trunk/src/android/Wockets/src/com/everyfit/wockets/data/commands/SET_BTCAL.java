/**
 * 
 */
package com.everyfit.wockets.data.commands;

import com.everyfit.wockets.data.types.BatteryCalibration;
/**
 * @author albinali
 *
 */
public final class SET_BTCAL extends Command {

	/**
	 *   
	 */
	public SET_BTCAL(BatteryCalibration cal) {
		// TODO Auto-generated constructor stub
		this._Bytes = new byte[] { (byte)0xa0,0,0,0,0,0,0,0,0,0};
		this._Bytes[0]|=(byte) CommandTypes.SET_BTCAL.ordinal();
		this._Bytes[1]=(byte) (byte) (cal._100Percentile>>3);
		this._Bytes[2]=(byte) (((cal._100Percentile&0x07)<<4)|(cal._80Percentile>>6));
		this._Bytes[3]=(byte) (((cal._80Percentile & 0x3f)<<1) |  (cal._60Percentile>>9));
		this._Bytes[4]=(byte) ((cal._60Percentile>>2) & 0x7f);
		this._Bytes[5]=(byte) (((cal._60Percentile&0x03)<<5)| (cal._40Percentile>>5));
		this._Bytes[6]=(byte) (((cal._40Percentile&0x1f)<<2)| (cal._20Percentile>>8));
		this._Bytes[7]=(byte) ((cal._20Percentile>>1)&0x7f);
		this._Bytes[8]=(byte) (((cal._20Percentile&0x01)<<6)|(cal._10Percentile>>4));
		this._Bytes[9]=(byte) ((cal._10Percentile&0x0f)<<3);
		
	}

}
