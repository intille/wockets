using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class AC_RSP : Response
    {

        public int _Count;
        public int _SeqNum;
        public double _TimeStamp;

        public AC_RSP(int id)
            : base(6, ResponseTypes.AC_RSP, (byte)id)
        {
        }
    }
}
