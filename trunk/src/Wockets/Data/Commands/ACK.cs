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
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.ACK, (byte)((seq >> 9) & 0x7f), (byte)((seq >> 2) & 0x7f), (byte)((seq & 0x03) << 5), (byte)0, (byte)0, (byte)0 };

            //this._Bytes[4] = (byte) (CRC8.Compute(0, this._Bytes, 4)>>1);
            //Compute the CRC on the first 4 bytes
            UInt16 crc = CRC16.Compute(this._Bytes, 4);
            this._Bytes[4] =(byte) (0x7f & (crc >> 9));
            this._Bytes[5] = (byte)(0x7f & (crc >> 2));
            this._Bytes[6] = (byte) ((crc&0x03) << 5);            
        }
    }
}
