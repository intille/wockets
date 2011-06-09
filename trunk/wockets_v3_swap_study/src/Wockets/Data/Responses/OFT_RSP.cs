using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class OFT_RSP : Response
    {

        public int _Offset;

        public OFT_RSP(int id)
            : base(3, ResponseTypes.OFT_RSP, (byte)id)
        {
        }
    }
}
