using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils.network.Bluetooth
{
    /// <summary>
    /// An enumeration that defines the different types of Bluetooth stacks that are supported
    /// </summary>
    public enum BluetoothStackTypes
    {
        /// <summary>
        /// Microsoft Bluetooth Stack
        /// </summary>
        Microsoft,

        /// <summary>
        /// Broadcom's Widcomm stack
        /// </summary>
        Widcomm,

        /// <summary>
        /// Unsupported stacks
        /// </summary>
        Unknown
    }
}
