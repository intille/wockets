using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class FV_RSP : Response
    {
        public int _Version = 0;
        public FV_RSP(int id)
            : base(2, ResponseTypes.FV_RSP, (byte)id)
        {
        }
    }
}
