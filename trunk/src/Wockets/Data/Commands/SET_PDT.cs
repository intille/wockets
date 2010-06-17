using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_PDT : Command
    {
        public SET_PDT(int timeout)
        {
            this.cmd = new byte[] { (byte)0xad, (byte)0 };
            cmd[1] = (byte)(((byte)timeout) & ((byte)0x7f));
            this.type = CommandTypes.SET_PDT;
        }
    }
}
