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
        SET_SENSORS,
        DISCONNECT
    }
}
