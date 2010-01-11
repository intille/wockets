#include "crc.h"


void init_crc(void){
	unsigned char remainder;
	int dividend=0;
	unsigned char bit;
	for (dividend=0;(dividend<256);++dividend)
	{
		remainder=dividend<< (WIDTH -8);

		for (bit=8;bit>0;--bit)
		{
			if (remainder & TOPBIT)
				remainder=(remainder<<1)^ POLYNOMIAL;
			else
				remainder=(remainder<<1);
		}

		crcTable[dividend]=remainder;
	}
}

unsigned char crc(unsigned char message[],unsigned char length)
{
	unsigned char data;
	unsigned char remainder=0;
	unsigned char byte=0;

	for (byte=0;(byte<length);byte++)
	{
		data=message[byte]^(remainder >> (WIDTH-8));
		remainder=crcTable[data] ^ (remainder<<8);
	}

	return remainder;
}
