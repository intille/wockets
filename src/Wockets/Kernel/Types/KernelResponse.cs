using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{
    public enum KernelResponse
    {
        STARTED,
        STOPPED,
        DISCOVERED,        
        CONNECTED,        
        DISCONNECTED,                
        SENSORS_UPDATED,        
        REGISTERED,        
        UNREGISTERED,        
        BATTERY_LEVEL_UPDATED,
        BATTERY_PERCENT_UPDATED,
        PC_COUNT_UPDATED,
        SENSITIVITY_UPDATED,
        CALIBRATION_UPDATED,
        SAMPLING_RATE_UPDATED,
        POWERDOWN_TIMEOUT_UPDATED,
        TRANSMISSION_MODE_UPDATED,
        MEMORY_MODE_UPDATED,
        ACTIVITY_COUNT_UPDATED
    }
}
