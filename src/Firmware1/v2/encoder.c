#include "encoder.h"

WOCKETS_UNCOMPRESSED_FRAME encode(unsigned char sensitivity,unsigned short x, unsigned short y, unsigned short z)
{
	WOCKETS_UNCOMPRESSED_FRAME frame;
	frame.byte1=0;
	frame.byte2=0;
	frame.byte3=0;
	frame.byte4=0;
	frame.byte5=0;
	
	//set the sync bit,no compession, length and channel
	frame.byte1 |= 0x80| ((unsigned char)((sensitivity&0x07)<<2)) | ((x>>8)& 0x03);
	frame.byte2 |= ((unsigned char) ((x>>1)&0x7f));
	frame.byte3 |= ((unsigned char) ((x<<6) &0x40)) | ((unsigned char) ((y>>4)&0x3f));
	frame.byte4 |= ((unsigned char) ((y<<3) &0x78)) | ((unsigned char) ((z>>7)&0x07));
	frame.byte5 |= ((unsigned char) (z&0x7f));

	return frame;
}
