using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class CRC16
    {

        public static UInt16 Compute(byte[] data, int len)
        {
            UInt16 crc = 0;
            for (int i = 0; (i < len); i++)
            {
                crc ^= (UInt16)(data[i] << 8);

                for (int j = 0; j < 8; ++j)
                {
                    if (((UInt16)(crc & 0x8000)) != 0)
                        crc = (UInt16)((UInt16)(crc << 1) ^ 0x1021);
                    else
                        crc = (UInt16)(crc << 1);
                }
            }
            return crc;
        }
    }
}
