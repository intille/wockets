using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class CRC8
    {
        private static int POLYNOMIAL = (0x1070 << 3);

        public static byte Compute(byte inCrc, byte inData)
        {
            int i;
            UInt16 data;
            data = (UInt16)(inCrc ^ inData);
            data <<= 8;
            for (i = 0; i < 8; i++)
            {
                if ((data & 0x8000) != 0)
                    data = (UInt16)(data ^ POLYNOMIAL);
                data = (UInt16)(data << 1);
            }
            return (byte)(data >> 8);
        }

        public static byte Compute(byte crc, byte[] data)
        {
            for (int i = 0; (i < data.Length); i++)
                crc = Compute(crc, data[i]);
            return crc;
        }


        public static byte Compute(byte crc, byte[] data, int len)
        {
            for (int i = 0; (i < len); i++)
                crc = Compute(crc, data[i]);
            return crc;
        }
    }
}
