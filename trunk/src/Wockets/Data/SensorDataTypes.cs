using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public enum SensorDataType : byte
    {
        BATTERYLEVEL,
        /// <summary>
        /// Mobile Sensor accelerometer data. 
        /// </summary>
        ACCEL,
        CALIBRATION
    }
}
