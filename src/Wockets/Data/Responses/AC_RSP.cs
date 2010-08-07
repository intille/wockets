using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class AC_RSP : Response
    {

        public int _Count;

        public AC_RSP(int id)
            : base(4, ResponseTypes.AC_RSP, (byte)id)
        {
        }
    }
}
