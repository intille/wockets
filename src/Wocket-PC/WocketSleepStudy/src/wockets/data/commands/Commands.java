/**
 * 
 */
package wockets.data.commands;

import java.io.IOException;

import java.io.OutputStream;

import wockets.data.types.BatteryCalibration;
import wockets.data.types.Calibration;
import wockets.data.types.LED;
import wockets.data.types.Sensitivity;
import wockets.data.types.TransmissionMode;


//import com.everyfit.wockets.apps.Application;


/**
 * @author Aida
 *
 */
public class Commands {
	
	public byte[] _Bytes;
	//RFCOMMReceiver wocketReceiver = (RFCOMMReceiver)Application._Controller._Sensors.get(0)._Receiver;
	//wocketReceiver.Write(_Bytes);
	
	//GET_BT, GET_BP, GET_PC, RST_BT, GET_SEN, GET_CAL, GET_SR, GET_ALT, GET_PDT,RST_WKT, 
    //ALIVE, PAUSE, RESUME, GET_TM, GET_BTCAL, GET_HV, GET_FV, GET_TCT, WKT_SHUTDOWN
    public void call(CommandTypes commandT, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0};		
		_Bytes[0]|=(byte) commandT.ordinal();
		outStream.write(_Bytes);
	}
	//SET_SR, SET_ALT, SET_PDT, ACK
	public void call(CommandTypes commandT, int param, OutputStream outStream) throws IOException{
		switch (commandT){
			case ACK:
				_Bytes = new byte[4];
				byte temp;
				temp = (byte)(param >> 8); //param is the sequence number
				_Bytes[0] = (byte)commandT.ordinal() ;
				_Bytes[1] = (byte)((byte)(temp >>> 1) & 0x7f);
				_Bytes[2] = (byte)((byte)(temp << 6) & 0x40);
				temp = (byte)(param);
				_Bytes[2] |= (byte)((byte)(temp >> 2) & 0x3f);
				_Bytes[3] = (byte) ((byte)(temp << 5) & 0x60);
				break;
			default:
				_Bytes = new byte[] {(byte)0xa0,0};
				_Bytes[0]|=(byte) commandT.ordinal();
				_Bytes[1]=(byte) (param&0x7f);
				break;
		}
		//outStream.write(_Bytes);
		for (int m=0; m<_Bytes.length; m++){
			outStream.write(_Bytes[m]);
			outStream.flush();
			try {
			Thread.sleep(200);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}
	// SET_TM, SET_VTM
	public void call(CommandTypes commandT, TransmissionMode mode, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (((byte)mode.ordinal()) << 4);	
		for (int m=0; m<2; m++){
			outStream.write(_Bytes[m]);
			try {
			Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}
	//SET_LED
	public void call(CommandTypes commandT, int second, LED led, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (((byte)(led.ordinal() & 0x01) << 6)|(second & 0x3f));
		for (int m=0; m<2; m++){
			outStream.write(_Bytes[m]);
			try {
			Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}	
	//SET_SEN
	public void call(CommandTypes commandT, Sensitivity sensitivity, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (((byte)sensitivity.ordinal())<<3);
		for (int m=0; m<2; m++){
			outStream.write(_Bytes[m]);
			try {
			Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}
	//SET_CAL
	public void call(CommandTypes commandT, Calibration cal, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0,0,0,0,0,0,0,0,0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (cal._X1G>>3);
		_Bytes[2]=(byte) (((cal._X1G&0x07)<<4)|(cal._XN1G>>6));
		_Bytes[3]=(byte) (((cal._XN1G & 0x3f)<<1) |  (cal._Y1G>>9));
		_Bytes[4]=(byte) ((cal._Y1G>>2) & 0x7f);
		_Bytes[5]=(byte) (((cal._Y1G&0x03)<<5)| (cal._YN1G>>5));
		_Bytes[6]=(byte) (((cal._YN1G&0x1f)<<2)| (cal._Z1G>>8));
		_Bytes[7]=(byte) ((cal._Z1G>>1)&0x7f);
		_Bytes[8]=(byte) (((cal._Z1G&0x01)<<6)|(cal._ZN1G>>4));
		_Bytes[9]=(byte) ((cal._ZN1G&0x0f)<<3);
		for (int m=0; m<10; m++){
			outStream.write(_Bytes[m]);
			try {
			Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}
	//SET_BTCAL
	public void call(CommandTypes commandT, BatteryCalibration cal, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0,0,0,0,0,0,0,0,0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (byte) (cal._100Percentile>>3);
		_Bytes[2]=(byte) (((cal._100Percentile&0x07)<<4)|(cal._80Percentile>>6));
		_Bytes[3]=(byte) (((cal._80Percentile & 0x3f)<<1) |  (cal._60Percentile>>9));
		_Bytes[4]=(byte) ((cal._60Percentile>>2) & 0x7f);
		_Bytes[5]=(byte) (((cal._60Percentile&0x03)<<5)| (cal._40Percentile>>5));
		_Bytes[6]=(byte) (((cal._40Percentile&0x1f)<<2)| (cal._20Percentile>>8));
		_Bytes[7]=(byte) ((cal._20Percentile>>1)&0x7f);
		_Bytes[8]=(byte) (((cal._20Percentile&0x01)<<6)|(cal._10Percentile>>4));
		_Bytes[9]=(byte) ((cal._10Percentile&0x0f)<<3);
		for (int m=0; m<10; m++){
			outStream.write(_Bytes[m]);
			try {
			Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}
	//SET_TCT
	public void call(CommandTypes commandT, int tct, int reps, int last, OutputStream outStream) throws IOException{
		_Bytes = new byte[] {(byte)0xa0,0,0,0,0,0,0,0,0,0};
		_Bytes[0]|=(byte) commandT.ordinal();_Bytes[1]=(byte) ((byte)tct>>1);
		_Bytes[2]=(byte) ((((byte)tct&0x01)<<6)|((byte)reps>>2));
		_Bytes[3]=(byte) ((((byte)reps & 0x03)<<5) |  ((byte)last>>3));
		_Bytes[4]=(byte) (((byte)last&0x07)<<4);
		for (int m=0; m<4; m++){
			outStream.write(_Bytes[m]);
			try {
			Thread.sleep(200);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		outStream.flush();
	}
	

}

