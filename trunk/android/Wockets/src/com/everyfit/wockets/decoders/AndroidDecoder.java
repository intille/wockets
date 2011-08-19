package com.everyfit.wockets.decoders;

import com.everyfit.wockets.utils.CircularBuffer;

public class AndroidDecoder extends Decoder 
{
	public AndroidDecoder(int id)
	{
		super(id,3072,10);
	}

	public AndroidDecoder(int id, int bufferSize, int packetSize) {
		super(id, bufferSize, packetSize);
		// TODO Auto-generated constructor stub
	}

	@Override
	public int Decode(int sensorID, CircularBuffer data, int start, int end) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean Initialize() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean Dispose() {
		// TODO Auto-generated method stub
		return false;
	}

}
