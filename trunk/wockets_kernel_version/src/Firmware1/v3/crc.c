#define  POLYNOMIAL (0x1070 << 3)

  unsigned char ComputeByte(unsigned char inCrc, unsigned char inData)
  {
     int i;
     unsigned short data;
     data = (unsigned short)(inCrc ^ inData);
     data <<= 8;
     for (i = 0; i < 8; i++)
     {
        if ((data & 0x8000) != 0)
        	data = (unsigned short)(data ^ POLYNOMIAL);
        data = (unsigned short)(data << 1);
     }
     return (unsigned char)(data >> 8);
   }

   
  unsigned char ComputeCRC8(unsigned char crc, unsigned char *data, int len)
  {
      for (int i = 0; (i < len); i++)
          crc = ComputeByte(crc, *(data+i));
       return crc;
  }

