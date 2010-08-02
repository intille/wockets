using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class PAUSE : Command
    {
        public PAUSE()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.PAUSE};
        }
    }
}
