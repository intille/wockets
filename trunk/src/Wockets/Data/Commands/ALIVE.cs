using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class ALIVE: Command
    {
        public ALIVE()
        {
            this.cmd = new byte[] { (byte)0xaf };
            this.type = CommandTypes.ALIVE;
        }
    }
}
