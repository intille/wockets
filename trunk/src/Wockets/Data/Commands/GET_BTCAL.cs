using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_BTCAL : Command
    {
        public GET_BTCAL()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.GET_BTCAL };
        }
    }
}
