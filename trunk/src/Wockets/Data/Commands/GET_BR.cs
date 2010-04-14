using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_BR : Command
    {

        public GET_BR()
        {
            this.cmd = new byte[] { (byte)'G', (byte)'U', (byte)13 };
            this.type = CommandTypes.GET_BAUD_RATE;
        }
    }
}
