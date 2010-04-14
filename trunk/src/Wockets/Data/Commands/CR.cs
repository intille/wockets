using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class CR : Command
    {
        public CR()
        {
            this.cmd = new byte[] { (byte)13 };
            this.type = CommandTypes.GET_BT;
        }
    }
}
