package com.everyfit.wockets.data;

public class AccelerationData extends SensorData {

	public short _X;
	public short _Y;
	public short _Z;
	
		public AccelerationData(int sensorID,int numRawBytes)
		{
			super(sensorID,numRawBytes,SensorDataType.UNCOMPRESSED_DATA_PDU);
		}	
		
		  
        public void Reset()
        {
            super.Reset();
            this._X = 0;
            this._Y = 0;
            this._Z = 0;
        }		
}
