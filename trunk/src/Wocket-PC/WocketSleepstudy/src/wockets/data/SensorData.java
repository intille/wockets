package wockets.data;

public abstract class SensorData {

	public SensorDataType _Type;
	public byte[] _RawBytes;
	public int _SensorID;
	public long _UnixTimeStamp;
	public int _Length;
	
	public SensorData(int sensorID,int numRawBytes,SensorDataType type){
		this._Type=type;
		this._RawBytes=new byte[numRawBytes];
		this._SensorID=sensorID;
	}
	
	public void Reset()
    {
        this._SensorID = 0;
        this._Type = SensorDataType.UNCOMPRESSED_DATA_PDU;
        for (int i = 0; i < this._RawBytes.length; i++)        
            this._RawBytes[i] = (byte)0;        
    }
}
