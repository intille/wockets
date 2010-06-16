using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public abstract class Response: SensorData
    {
        public const byte MAX_RAW_BYTES = 10;
        public ResponseTypes _Type;
        public Response(byte numRawBytes,ResponseTypes type, byte sensorID):base(numRawBytes,SensorDataType.RESPONSE_PDU,sensorID)
        {
            _Type = type;
        }

    }
}
