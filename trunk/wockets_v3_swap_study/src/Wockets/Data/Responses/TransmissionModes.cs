using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public enum TransmissionModes: byte
    {
        Continuous=0,
        Bursty30=1,
        Bursty60=2,
        Bursty90=3,
        Bursty120=4
    }
}
