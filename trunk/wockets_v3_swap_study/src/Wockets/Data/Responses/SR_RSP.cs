using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class SR_RSP: Response
    {
        public int _SamplingRate = 0;
        public SR_RSP(int id)
            : base(2, ResponseTypes.SR_RSP, (byte)id)
        {
        }
    }
}
