using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class ALT_RSP: Response
    {
        public int _AliveTimer;

        public ALT_RSP(int id)
            : base(2, ResponseTypes.ALT_RSP, (byte)id)
        {
        }
    }
}
