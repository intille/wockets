using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_ALT : Command
    {
        public GET_ALT()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.GET_ALT };
        }
    }
}
