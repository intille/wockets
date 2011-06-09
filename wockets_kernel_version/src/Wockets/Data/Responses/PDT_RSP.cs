using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class PDT_RSP: Response
    {
        public int _Timeout = 0;
        public PDT_RSP(int id)
            : base(2, ResponseTypes.PDT_RSP, (byte)id)
        {
        }
    }
}
