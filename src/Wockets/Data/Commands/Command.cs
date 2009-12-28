using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public abstract class Command
    {
        protected CommandTypes type;
        protected byte[] cmd;

        public byte[] _Bytes
        {
            get
            {
                return this.cmd;
            }
        }

        public CommandTypes _Type
        {
            get
            {
                return this.type;
            }
        }
    }
}
