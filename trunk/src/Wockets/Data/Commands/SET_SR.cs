using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_SR : Command
    {
        public SET_SR(int sr)
        {
            this.cmd = new byte[] { (byte)0xa9, (byte)0 };
            cmd[1] = (byte) (((byte)sr) & ((byte)0x7f));
            this.type = CommandTypes.SET_SR;
        }
    }
}
