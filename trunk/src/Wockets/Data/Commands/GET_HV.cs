using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_HV : Command
    {
        public GET_HV()
        {
            this.cmd = new byte[] { (byte)0xb6 };
            this.type = CommandTypes.GET_HV;
        }
    }
}
