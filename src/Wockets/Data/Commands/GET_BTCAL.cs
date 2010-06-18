using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_BTCAL : Command
    {
        public GET_BTCAL()
        {
            this.cmd = new byte[] { (byte)0xb4 };
            this.type = CommandTypes.GET_BTCAL;
        }
    }
}
