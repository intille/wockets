using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_PC: Command
    {
        public GET_PC()
        {
            this.cmd = new byte[] { (byte)0xa1 };
            this.type = CommandTypes.GET_PC;
        }
    }
}
