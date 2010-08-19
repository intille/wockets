using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{
    public enum KernelResponse: byte
    {
        STARTED=0,
        STOPPED=1,
        DISCOVERED=2,        
        CONNECTED=3,        
        DISCONNECTED=4,                
        SENSORS_UPDATED=5,        
        REGISTERED=6,        
        UNREGISTERED=7,        
        BATTERY_LEVEL_UPDATED=8,
        BATTERY_PERCENT_UPDATED=9,
        PC_COUNT_UPDATED=10,
        SENSITIVITY_UPDATED=11,
        CALIBRATION_UPDATED=12,
        SAMPLING_RATE_UPDATED=13,
        POWERDOWN_TIMEOUT_UPDATED=14,
        TRANSMISSION_MODE_UPDATED=15,
        MEMORY_MODE_UPDATED=16,
        ACTIVITY_COUNT_UPDATED=17
    }
}
