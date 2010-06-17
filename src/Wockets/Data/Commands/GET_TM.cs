using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_TM : Command
    {
        public GET_TM()
        {
            this.cmd = new byte[] { (byte)0xb2 };
            this.type = CommandTypes.GET_TM;
        }
    }
}
