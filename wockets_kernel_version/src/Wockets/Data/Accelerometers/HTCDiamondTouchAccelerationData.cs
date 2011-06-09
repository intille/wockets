using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    /// <summary>
    /// A sealed class that represents an internal accelerometer data unit for HTC diamond touch phones
    /// </summary>
    public sealed class HTCDiamondTouchAccelerationData : AccelerationData
    {
        /// <summary>
        /// Size of the accelerometer data unit for HTC diamond touch
        /// </summary>
        public const byte NUM_RAW_BYTES = 16;

        /// <summary>
        /// The constructor for the accelerometer data unit for HTC diamond touch phones when used with wockets
        /// </summary>
        /// <param name="sensorID">ID of the internal accelerometer</param>
        public HTCDiamondTouchAccelerationData(byte sensorID)
            : base(NUM_RAW_BYTES,sensorID)            
        {           
        }

        /// <summary>
        /// The constructor for the accelerometer data unit of HTC diamond touch phone when used alone
        /// </summary>
        public HTCDiamondTouchAccelerationData()
            : base(NUM_RAW_BYTES, 0)
        {
        }
    }
}
