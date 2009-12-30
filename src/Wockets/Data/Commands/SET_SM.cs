using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_SM : Command
    {
        public SET_SM(ushort sleep_time)
        {
            char[] hex = ((int)(sleep_time / 0.625)).ToString("X4").ToCharArray();
            this.cmd = new byte[8];
            this.cmd[0] = (byte)'S';
            this.cmd[1] = (byte)'W';
            this.cmd[2] = (byte)',';
            for (int i = 0; (i < 4); i++)
                this.cmd[i + 3] = (byte)hex[i];
            this.cmd[7] = 13;
            this.type = CommandTypes.SET_SM;
        }
    }
}
