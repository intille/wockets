using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class ALIVE: Command
    {
        public ALIVE()
        {
            this.cmd = new byte[] { (byte)0xbb };
            this.type = CommandTypes.GET_BT;
        }
    }
}
