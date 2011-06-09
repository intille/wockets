using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public abstract class Response: SensorData
    {
        public const byte MAX_RAW_BYTES = 10;

        public Response(byte numRawBytes,SensorDataType type, byte sensorID):base(numRawBytes,type,sensorID)
        {
        }

    }
}
