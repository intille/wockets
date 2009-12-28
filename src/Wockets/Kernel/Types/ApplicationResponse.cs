using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{
    public enum ApplicationResponse
    {
        DISCOVERY_COMPLETED,
        CONNECT_SUCCESS,
        DISCONNECT_SUCCESS,
        CONNECT_FAILURE,
        DISCONNECT_FAILURE,
        SET_SENSORS_SUCCESS,
        SET_SENSORS_FAILURE
    }
}
