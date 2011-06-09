using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_BP : Command
    {
        public GET_BP()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.GET_BP };
        }
    }
}
