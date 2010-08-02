using System;

using Wockets.Data.Types;

namespace Wockets.Data.Commands
{
    public class SET_TM : Command
    {

        public SET_TM(TransmissionMode mode)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_TM, (byte)(((byte)mode) << 4) };
        }
    }
}
