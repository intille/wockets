using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class ACC_RSP : Response
    {

        public int _Count;

        public ACC_RSP(int id)
            : base(3, ResponseTypes.ACC_RSP, (byte)id)
        {
        }
    }
}
