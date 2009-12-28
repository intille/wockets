#include "encoder.h"

WOCKETS_UNCOMPRESSED_FRAME encode(unsigned short channel,unsigned short x, unsigned short y, unsigned short z, unsigned char crc)
{
	WOCKETS_UNCOMPRESSED_FRAME frame;
	frame.byte1=0;
	frame.byte2=0;
	frame.byte3=0;
	frame.byte4=0;
	frame.byte5=0;
	frame.byte6=0;
	frame.byte7=0;

	//set the sync bit,no compession, length and channel
	frame.byte1 |= 0x80| ((unsigned char)(channel<<3)) | UNCOMPRESSED_LENGTH;
	frame.byte2 |= (crc>>1);
	frame.byte3 |= ((crc<<7)>>1) | ((unsigned char) ((x>>4)&0x3f));
	frame.byte4 |=  ((unsigned char) ((x<<3) &0x78)) | ((unsigned char) ((y>>7)&0x07));
	frame.byte5 |= ((unsigned char) (y&0x7f));
	frame.byte6 |= ((unsigned char) ((z>>3)&0x7f));
	frame.byte7 |= ((unsigned char) ((z<<4)&0x70));

	return frame;
}
