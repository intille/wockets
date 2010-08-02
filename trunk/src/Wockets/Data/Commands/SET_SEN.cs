using System;

using Wockets.Data.Types;

namespace Wockets.Data.Commands
{
    public class SET_SEN: Command
    {

        public SET_SEN(Sensitivity sensitivity)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_SEN, (byte)(((byte)sensitivity)<<3) };          
        }
    }
}
