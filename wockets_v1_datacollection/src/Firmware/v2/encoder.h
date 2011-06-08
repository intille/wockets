#define CHANNEL 0x17 
//23 decimal
#define UNCOMPRESSED_LENGTH 0x2 
// counts bytes after the first 2

typedef struct{
	char byte1; //sync bit, 2 bits packet type, 3 bits sensitivity, 2 bits MSB X
	char byte2;	//0 bit, 7 X
	char byte3; // 0 bit, 1 LSB X, 6 MSB y
	char byte4; // 0 bit, 4 LSB y, 3 MSB z
	char byte5; // 0 bit, 7 LSB z
} WOCKETS_UNCOMPRESSED_FRAME;

WOCKETS_UNCOMPRESSED_FRAME encode(unsigned char sensitivity,unsigned short x, unsigned short y, unsigned short z);
