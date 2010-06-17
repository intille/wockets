using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_BP : Command
    {
        public GET_BP()
        {
            this.cmd = new byte[] { (byte)0xa1 };
            this.type = CommandTypes.GET_BP;
        }
    }
}
