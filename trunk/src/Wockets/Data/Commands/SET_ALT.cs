using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_ALT : Command
    {
        public SET_ALT(int timeout)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_ALT,
                                  (byte) (timeout&0x7f)};
        }
    }
}
