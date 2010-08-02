using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_PC: Command
    {
        public GET_PC()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.GET_PC };
        }
    }
}
