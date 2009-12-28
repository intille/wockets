using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class BT_RST: Command
    {
        public BT_RST()
        {
            this.cmd = new byte[] { (byte)'R', (byte)',', (byte)'1' };
            this.type = CommandTypes.BT_RST;               
        }
    }
}
