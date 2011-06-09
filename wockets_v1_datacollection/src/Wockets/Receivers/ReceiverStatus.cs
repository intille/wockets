using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Receivers
{
    public enum ReceiverStatus
    {
        Reconnecting,
        Disconnected,
        Connected,
        Disposed
    }
}
