using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_CAL : Command
    {
        public GET_CAL()
        {
            this.cmd = new byte[] { (byte)0xa6 };
            this.type = CommandTypes.GET_CAL;
        }
    }
}
