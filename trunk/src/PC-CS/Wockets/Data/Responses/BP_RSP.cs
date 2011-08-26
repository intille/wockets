using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class BP_RSP: Response
    {
        public int _Percent;

        public BP_RSP(int id)
            : base(2, ResponseTypes.BP_RSP, (byte)id)
        {
        }
    }
}
