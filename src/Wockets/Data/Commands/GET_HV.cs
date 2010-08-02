using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class GET_HV : Command
    {
         public GET_HV()
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.GET_HV };
        }
    }
}
