using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_SR: Command
    {
        public GET_SR()
        {
            this.cmd = new byte[] { (byte)0xa8 };
            this.type = CommandTypes.GET_SR;
        }
    }
}
