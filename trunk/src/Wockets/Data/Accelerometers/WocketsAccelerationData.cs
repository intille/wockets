using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    public sealed class WocketsAccelerationData: AccelerationData
    {
        public const byte NUM_RAW_BYTES = 5;

        public WocketsAccelerationData(byte sensorID): base(NUM_RAW_BYTES,sensorID)
        {           
        }

        public WocketsAccelerationData()
            : base(NUM_RAW_BYTES, 0)
        {
        }
    }
}
