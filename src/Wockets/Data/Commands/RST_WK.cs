using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class RST_WK: Command  //10110
    {
        public RST_WK()
        {
            this.cmd = new byte[] { (byte)0xb6 };
            this.type = CommandTypes.RST_WKT;
        }
    }
}
