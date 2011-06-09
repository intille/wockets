using System;
using Wockets.Data.Types;

namespace Wockets.Data.Commands
{
    public class SET_VTM : Command
    {

        public SET_VTM(TransmissionMode mode)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_VTM, (byte)(((byte)mode) << 4) };
        }
    }
}
