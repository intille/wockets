/**
 * 
 */
package wockets.data.commands;

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
    //ALIVE, PAUSE, RESUME, GET_TM, GET_BTCAL, GET_HV, GET_FV, GET_TCT, ACK, WKT_SHUTDOWN
    public void call(CommandTypes commandT){
		_Bytes = new byte[] {(byte)0xa0};		
		_Bytes[0]|=(byte) commandT.ordinal();	
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}
	//SET_SR, SET_ALT, SET_PDT
	public void call(CommandTypes commandT, int param){
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (param&0x7f);
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}
	// SET_TM, SET_VTM
	public void call(CommandTypes commandT, TransmissionMode mode){
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (((byte)mode.ordinal()) << 4);	
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}
	//SET_LED
	public void call(CommandTypes commandT, int second, LED led){
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (((byte)(led.ordinal() & 0x01) << 6)|(second & 0x3f));
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);		
	}	
	//SET_SEN
	public void call(CommandTypes commandT, Sensitivity sensitivity){
		_Bytes = new byte[] {(byte)0xa0,0};
		_Bytes[0]|=(byte) commandT.ordinal();
		_Bytes[1]=(byte) (((byte)sensitivity.ordinal())<<3);
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}
	//SET_CAL
	public void call(CommandTypes commandT, Calibration cal){
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
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}
	//SET_BTCAL
	public void call(CommandTypes commandT, BatteryCalibration cal){
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
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}
	//SET_TCT
	public void call(CommandTypes commandT, int tct, int reps, int last){
		_Bytes = new byte[] {(byte)0xa0,0,0,0,0,0,0,0,0,0};
		_Bytes[0]|=(byte) commandT.ordinal();_Bytes[1]=(byte) ((byte)tct>>1);
		_Bytes[2]=(byte) ((((byte)tct&0x01)<<6)|((byte)reps>>2));
		_Bytes[3]=(byte) ((((byte)reps & 0x03)<<5) |  ((byte)last>>3));
		_Bytes[4]=(byte) (((byte)last&0x07)<<4);
		//((RFCOMMReceiver)WocketsService._Controller._Sensors.get(0)._Receiver).Write(_Bytes);
	}	

}

