using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{
    public enum KernelCommand
    {
        REGISTER,
        UNREGISTER,
        DISCOVER,
        CONNECT,
        SET_WOCKETS,
        DISCONNECT,
        GET_BATTERY_LEVEL,
        GET_BATTERY_PERCENT,
        GET_PDU_COUNT,
        GET_WOCKET_SENSITIVITY,
        SET_WOCKET_SENSITIVITY,
        GET_WOCKET_CALIBRATION,
        SET_WOCKET_CALIBRATION,
        GET_WOCKET_SAMPLING_RATE,
        SET_WOCKET_SAMPLING_RATE,
        GET_WOCKET_POWERDOWN_TIMEOUT,
        SET_WOCKET_POWERDOWN_TIMEOUT,
        GET_TRANSMISSION_MODE,
        SET_TRANSMISSION_MODE,
        GET_MEMORY_MODE,
        SET_MEMORY_MODE,        
        TERMINATE
    }
}
