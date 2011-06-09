using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class RESUME : Command
    {
        public RESUME()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.RESUME};
        }
    }
}
