using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_PDT : Command
    {
        public SET_PDT(int timeout)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_PDT,
                                  (byte) (timeout&0x7f)};
        }
    }
}
