using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_FV : Command
    {
        public GET_FV()
        {
            this.cmd = new byte[] { (byte)0xb7 };
            this.type = CommandTypes.GET_FV;
        }
    }
}
