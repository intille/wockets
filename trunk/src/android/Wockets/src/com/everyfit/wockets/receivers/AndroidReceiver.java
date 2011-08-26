package com.everyfit.wockets.receivers;

import java.util.ArrayList;

import com.everyfit.wockets.data.commands.Command;
import com.everyfit.wockets.data.types.TransmissionMode;

public class AndroidReceiver extends Receiver
{
	private final String TAG = "AndroidReceiver";
	private static final int BUFFER_SIZE = 1024;	
	//private static final int SEND_BUFFER_SIZE = 256;	
	public String _Address;
	public ArrayList<Command> _OnConnectionCommands = new ArrayList<Command>();
	public TransmissionMode _TransmissionMode=  TransmissionMode.Continuous;
	//public BluetoothStream _BluetoothStream;
	//public long _CurrentConnectionUnixTime = 0;
	//public int _Reconnections = 0;
	//public int _SuccessfulConnections = 0;
	//public ReconnectionThread reconnectionThread=null;

	public AndroidReceiver(int id) 
	{
		super(id);
		// TODO Auto-generated constructor stub
	}

	@Override
	public boolean Initialize() 
	{
		this._Status = ReceiverStatus.Connected;
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean Dispose() 
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void CheckStatus() 
	{
		// TODO Auto-generated method stub
		
	}

	@Override
	public int getReconnections() 
	{
		// TODO Auto-generated method stub
		return 0;
	}

}
