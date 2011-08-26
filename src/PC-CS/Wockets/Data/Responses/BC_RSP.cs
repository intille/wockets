using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{ 
    public class BC_RSP : Response
    {

        public int _Count;

        public BC_RSP(int id)
            : base(3, ResponseTypes.BC_RSP, (byte)id)
        {
        }
    }
}
