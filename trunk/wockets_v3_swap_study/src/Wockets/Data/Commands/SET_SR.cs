using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_SR : Command
    {
        public SET_SR(int sr)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_SR,
                                  (byte) (sr&0x7f)};
        }
    }
}
