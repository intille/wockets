using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Receivers
{
    public interface Radio_CMD
    {

        bool LowPower
        {
            get;
            set;
        }

        void Reset();
    }
}
