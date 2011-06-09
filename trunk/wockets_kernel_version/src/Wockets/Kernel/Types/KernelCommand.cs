using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{
    /// <summary>
    /// Commands that an application can send to the kernel
    /// </summary>
    public enum KernelCommand
    {
        /// <summary>
        /// Registers an application
        /// </summary>
        REGISTER,

        /// <summary>
        /// Unregisters an application
        /// </summary>
        UNREGISTER,

        /// <summary>
        /// Discovers wockets
        /// </summary>
        DISCOVER,

        /// <summary>
        /// Connects to wockets
        /// </summary>
        CONNECT,

        /// <summary>
        /// Sets wockets to connect to
        /// </summary>
        SET_WOCKETS,

        /// <summary>
        /// Disconnects from wockets
        /// </summary>
        DISCONNECT,

        /// <summary>
        /// Get battery level for a wocket
        /// </summary>
        GET_BATTERY_LEVEL,

        /// <summary>
        /// Get battery percent for a wocket
        /// </summary>
        GET_BATTERY_PERCENT,

        /// <summary>
        /// Get number of sent packets from a wocket
        /// </summary>
        GET_PDU_COUNT,

        /// <summary>
        /// Get sensitivity of a wocket
        /// </summary>
        GET_WOCKET_SENSITIVITY,

        /// <summary>
        /// Set sensitivity of a wocket
        /// </summary>
        SET_WOCKET_SENSITIVITY,

        /// <summary>
        /// Get calibration values for a wocket
        /// </summary>
        GET_WOCKET_CALIBRATION,

        /// <summary>
        /// Set calibration values for a wocket
        /// </summary>
        SET_WOCKET_CALIBRATION,

        /// <summary>
        /// Get sampling rate for a wocket
        /// </summary>
        GET_WOCKET_SAMPLING_RATE,

        /// <summary>
        /// Set sampling rate for a wocket
        /// </summary>
        SET_WOCKET_SAMPLING_RATE,

        /// <summary>
        /// Get power down timeout for a wocket
        /// </summary>
        GET_WOCKET_POWERDOWN_TIMEOUT,

        /// <summary>
        /// Set power down timeout for a wocket
        /// </summary>
        SET_WOCKET_POWERDOWN_TIMEOUT,

        /// <summary>
        /// Get transmission mode for a wocket
        /// </summary>
        GET_TRANSMISSION_MODE,

        /// <summary>
        /// Set transmission mode for a wocket
        /// </summary>
        SET_TRANSMISSION_MODE,

        /// <summary>
        /// Get memory mode for the kernel
        /// </summary>
        GET_MEMORY_MODE,

        /// <summary>
        /// Set memory mode for the kernel
        /// </summary>
        SET_MEMORY_MODE,

        /// <summary>
        /// Terminate and exit the kernel
        /// </summary>
        TERMINATE,

        /// <summary>
        /// Pings the kernel
        /// </summary>
        PING,
        
        GET_TCT,

        SET_TCT
    }
}
