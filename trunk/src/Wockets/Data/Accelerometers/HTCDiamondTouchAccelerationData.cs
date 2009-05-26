using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    public sealed class HTCDiamondTouchAccelerationData : AccelerationData
    {
        public const byte NUM_RAW_BYTES = 16;

        public HTCDiamondTouchAccelerationData(byte sensorID)
            : base(NUM_RAW_BYTES,sensorID)            
        {           
        }

        public HTCDiamondTouchAccelerationData()
            : base(NUM_RAW_BYTES, 0)
        {
        }
    }
}
