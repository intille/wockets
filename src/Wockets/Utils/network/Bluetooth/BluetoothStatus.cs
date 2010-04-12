using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils.network.Bluetooth
{
    public enum BluetoothStatus
    {
        /// <summary>
        /// Stack is up and running
        /// </summary>
        Up,

        /// <summary>
        /// Stack is down and not running
        /// </summary>
        Down,

        /// <summary>
        /// Stack produced an error
        /// </summary>
        Error,

        /// <summary>
        /// Bluetooth stream is reconnecting
        /// </summary>
        Reconnecting,

        /// <summary>
        /// Bluetooth stream is disconnected
        /// </summary>
        Disconnected,

        /// <summary>
        /// Bluetooth stream is active and connected
        /// </summary>
        Connected
    }
}
