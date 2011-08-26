using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_CAL : Command
    {
         public GET_CAL()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.GET_CAL };
        }
    }
}
