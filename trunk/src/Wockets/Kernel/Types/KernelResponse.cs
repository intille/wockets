using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{

    /// <summary>
    /// Specifies responses that the kernel sends
    /// </summary>
    public enum KernelResponse: byte
    {

        /// <summary>
        /// Kernel started
        /// </summary>
        STARTED=0,

        /// <summary>
        /// Kernel stopped
        /// </summary>
        STOPPED=1,

        /// <summary>
        /// Wockets discovered
        /// </summary>
        DISCOVERED=2,        

        /// <summary>
        /// Wockets connected
        /// </summary>
        CONNECTED=3,        

        /// <summary>
        /// Wockets disconnected
        /// </summary>
        DISCONNECTED=4,         
       
        /// <summary>
        /// Wockets to connect to got updated
        /// </summary>
        SENSORS_UPDATED=5,       


        /// <summary>
        /// Application successfully registered with the kernel
        /// </summary>
        REGISTERED=6,        

        /// <summary>
        /// Application successfully unregistered with the kernel
        /// </summary>
        UNREGISTERED=7,        

        /// <summary>
        /// Battery level got updated for at least 1 wocket
        /// </summary>
        BATTERY_LEVEL_UPDATED=8,

        /// <summary>
        /// Battery percent got updated for at least 1 wocket
        /// </summary>
        BATTERY_PERCENT_UPDATED=9,

        /// <summary>
        /// Sent packet count got updated for at least 1 wocket
        /// </summary>
        PC_COUNT_UPDATED=10,

        /// <summary>
        /// Sensitivity got updated for at least 1 wocket
        /// </summary>
        SENSITIVITY_UPDATED=11,

        /// <summary>
        /// Calibration values got updated for at least 1 wocket
        /// </summary>
        CALIBRATION_UPDATED=12,

        /// <summary>
        /// Sampling rate got updated for at least 1 wocket
        /// </summary>
        SAMPLING_RATE_UPDATED=13,

        /// <summary>
        /// Power down timeout got updated for at least 1 wocket
        /// </summary>
        POWERDOWN_TIMEOUT_UPDATED=14,

        /// <summary>
        /// Transmission mode got updated for at least 1 wocket
        /// </summary>
        TRANSMISSION_MODE_UPDATED=15,

        /// <summary>
        /// Memory mode got update for the kernel
        /// </summary>
        MEMORY_MODE_UPDATED=16,

        /// <summary>
        /// Activity count got update for at least 1 wocket
        /// </summary>
        ACTIVITY_COUNT_UPDATED=17,

        /// <summary>
        /// Ping response
        /// </summary>
        PING_RESPONSE=18,

        CONNECT_FAILED=19,
        DISCONNECT_FAILED=20,
        SENSORS_UPDATED_FAILED=21,
        TCT_UPDATED=22
    }
}
