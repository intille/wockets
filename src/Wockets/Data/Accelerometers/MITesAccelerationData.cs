using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    public sealed class MITesAccelerationData : AccelerationData
    {
        public const byte NUM_RAW_BYTES = 5;

        public MITesAccelerationData(byte sensorID)
            : base(NUM_RAW_BYTES,sensorID)
        {
   
        }

        public MITesAccelerationData()
            : base(NUM_RAW_BYTES, 0)
        {
        }

    }
}
