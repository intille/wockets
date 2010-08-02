using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class RST_WK: Command  
    {
        public RST_WK()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.RST_WKT };
        }
    }
}
