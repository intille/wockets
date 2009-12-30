using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class PAUSE : Command
    {
        public PAUSE()
        {
            this.cmd = new byte[] { (byte)0xbc };
            this.type = CommandTypes.ALIVE;
        }
    }
}
