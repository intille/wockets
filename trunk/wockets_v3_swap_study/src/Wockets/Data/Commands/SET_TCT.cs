using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_TCT : Command
    {
        public SET_TCT(int tct,int reps,int last)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_TCT,
                (byte) ((byte)tct>>1),
                (byte) ((((byte)tct&0x01)<<6)|((byte)reps>>2)),
                (byte) ((((byte)reps & 0x03)<<5) |  ((byte)last>>3)),               
                (byte) (((byte)last&0x07)<<4)};
        }
    }
}
