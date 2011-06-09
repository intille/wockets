using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public enum SensorDataType : byte
    {
        UNCOMPRESSED_DATA_PDU=0,
        COMMAND_PDU=1,
        RESPONSE_PDU=2, 
        COMPRESSED_DATA_PDU=3           
    }
}
