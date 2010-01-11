using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_SM: Command
    {
        public GET_SM()
        {            
            this.cmd = new byte[] { (byte)'G', (byte)'W', (byte)13 };
            this.type = CommandTypes.GET_SM;
        }
    }
}
