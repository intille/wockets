package com.everyfit.wockets.utils;

public class CircularBuffer {

	public byte[] _Bytes;
	public double[] _Timestamp;
	public int _Head;
	public int _Tail;
	
	public CircularBuffer(int size)
	{
		this._Bytes=new byte[size];
		this._Timestamp= new double[size];
		this._Head=0;
		this._Tail=0;
	}
	
	public static void BlockCopy(byte[] src,int srcOffset,byte[] dst,int dstOffset,int count){		
		for (int i=0;(i<count);i++)
			dst[dstOffset++]=src[srcOffset++];		
	}
	
}
