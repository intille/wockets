using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils.network.Bluetooth
{
    public enum BluetoothStatus
    {
        Up,
        Down,
        Error,
        Reconnecting,
        Disconnected,
        Connected,
        Disposed,
        Unloaded
    }
}
