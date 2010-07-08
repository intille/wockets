using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    public abstract class AccelerationData: SensorData
    {
        /// <summary>
        /// The x value of an accelerometer
        /// </summary>
        public short _X;

        /// <summary>
        /// The y value of an accelerometer
        /// </summary>
        public short _Y;

        /// <summary>
        /// The z value of an accelerometer
        /// </summary>
        public short _Z;




        public AccelerationData(byte numRawBytes,byte sensorID)
            : base(numRawBytes, SensorDataType.UNCOMPRESSED_DATA_PDU, sensorID)
        {
  
        }


        public void Reset()
        {
            base.Reset();
            this._X = 0;
            this._Y = 0;
            this._Z = 0;
        }



    }
}
