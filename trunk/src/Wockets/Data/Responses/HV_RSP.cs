using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class HV_RSP : Response
    {
        public int _Version = 0;
        public HV_RSP(int id)
            : base(2, ResponseTypes.HV_RSP, (byte)id)
        {
        }
    }
}
