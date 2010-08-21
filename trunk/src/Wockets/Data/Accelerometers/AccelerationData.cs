using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    /// <summary>
    /// An abstract class that represents a generic triaxial accelerometer data unit
    /// </summary>
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

        /// <summary>
        /// The constructor that intializes the accelerometer data unit
        /// </summary>
        /// <param name="numRawBytes">Size of the raw accelerometer PDU</param>
        /// <param name="sensorID">ID of the accelerometer</param>
        public AccelerationData(byte numRawBytes,byte sensorID)
            : base(numRawBytes, SensorDataType.UNCOMPRESSED_DATA_PDU, sensorID)
        {
 
        }

        /// <summary>
        /// Re-initializes the values for the accelerometer's 3 axes to 0
        /// </summary>
        public void Reset()
        {
            base.Reset();
            this._X = 0;
            this._Y = 0;
            this._Z = 0;
        }

    }
}
