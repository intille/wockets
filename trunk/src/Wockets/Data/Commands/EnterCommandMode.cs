using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class EnterCommandMode: Command
    {
        public EnterCommandMode()
        {
            this.cmd = new byte[] { (byte)36, (byte)36, (byte)36 };
            this.type = CommandTypes.ENTER_CMD_MODE;
        }
    }
}
