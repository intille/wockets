using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class PC_RSP: Response
    {
        public int _Count;
        public PC_RSP(int id)
            : base(6, ResponseTypes.PC_RSP, (byte)id)
        {
        }
    }
}
