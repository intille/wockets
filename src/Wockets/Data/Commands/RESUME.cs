using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class RESUME : Command
    {
        public RESUME()
        {
            this.cmd = new byte[] { (byte)0xbd };
            this.type = CommandTypes.GET_BT;
        }
    }
}
