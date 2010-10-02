using System;

using System.Collections.Generic;
using System.Text;
using Wockets.Utils;
namespace Wockets.Data.Commands
{
    public class ACK : Command
    {

        public ACK(int seq)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.ACK, (byte)((seq >> 9) & 0x7f), (byte)((seq >> 2) & 0x7f), (byte)((seq & 0x03)<<5), (byte) 0 };
            

            //Compute the CRC on the first 4 bytes
            this._Bytes[4] = (byte) (CRC8.Compute(0, this._Bytes, 4)>>1);
        }
    }
}
