using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_SEN: Command
    {
        public GET_SEN()
        {
            this.cmd = new byte[] { (byte)0xa4 };
            this.type = CommandTypes.GET_SEN;
        }
    }
}
