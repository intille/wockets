using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class BL_RSP: Response
    {

        public int _BatteryLevel;

        public BL_RSP(int id)
            : base(3, ResponseTypes.BL_RSP, (byte)id)
        {
        }
    }
}
