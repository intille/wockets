using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{

    public sealed class SparkfunAccelerationData:AccelerationData
    {
        public const byte NUM_RAW_BYTES = 15;

        public SparkfunAccelerationData(byte sensorID)
            : base(NUM_RAW_BYTES,sensorID)            
        {           
        }

        public SparkfunAccelerationData()
            : base(NUM_RAW_BYTES, 0)
        {
        }
    }
}
