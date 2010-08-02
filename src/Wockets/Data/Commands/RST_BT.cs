using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class RST_BT : Command
    {
        public RST_BT()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.RST_BT };
        }
    }
}
