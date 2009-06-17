using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public abstract class ReceiverCommand
    {
        protected CommandTypes type;
        protected byte[] cmd;

        public byte[] CMD
        {
            get
            {
                return this.cmd;
            }
        }

        public CommandTypes Type
        {
            get
            {
            return this.type;
            }
        }
    }
}
