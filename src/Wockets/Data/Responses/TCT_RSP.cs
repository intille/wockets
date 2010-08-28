using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class TCT_RSP : Response
    {

        public int _TCT;
        public int _REPS;
        public int _LAST;

        public TCT_RSP(int id)
            : base(5, ResponseTypes.TCT_RSP, (byte)id)
        {
        }
    }
}
