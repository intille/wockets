#define CHANNEL 0x17 
//23 decimal
#define UNCOMPRESSED_LENGTH 0x2 
// counts bytes after the first 2

typedef struct{
	char byte1; //sync bit, compression flag, 3 bits lenght, 3 bits channel
	char byte2;	//0 bit, 7 crc
	char byte3; // 0 bit, 1 crc, 6 MSB x
	char byte4; // 0 bit, 4 LSB x, 3 MSB Y
	char byte5; // 0 bit, 7 LSB Y
	char byte6; // 0 bit, 7 MSB Z
	char byte7; // 0 bit, 3 LSB Z, 4 unused

} WOCKETS_UNCOMPRESSED_FRAME;

WOCKETS_UNCOMPRESSED_FRAME encode(unsigned short channel,unsigned short x, unsigned short y, unsigned short z, unsigned char crc);
