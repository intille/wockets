using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Types
{
    public enum TransmissionMode: byte
    {
        Continuous=0,
        Bursty30=1,
        Bursty60=2,
        Bursty90=3,
        Bursty120=4
    }
}
