using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_PDT : Command
    {
        public GET_PDT()
        {
            this.cmd = new byte[] { (byte)0xac };
            this.type = CommandTypes.GET_PDT;
        }
    }
}
