using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class ExitCommandMode:Command
    {
        public ExitCommandMode()
        {
            this.cmd = new byte[] { (byte)'-', (byte)'-', (byte)'-', (byte)13 };
            this.type = CommandTypes.EXIT_CMD_MODE;
        }
    }
}
