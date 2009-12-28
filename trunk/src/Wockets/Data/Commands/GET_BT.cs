using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_BT: Command
    {
        public GET_BT()
        {
            this.cmd = new byte[] { (byte)0xa0 };
            this.type = CommandTypes.GET_BT;
        }
    }
}
