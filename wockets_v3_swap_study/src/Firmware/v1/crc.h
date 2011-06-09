#define POLYNOMIAL 0xD8
#define WIDTH (8 *sizeof(unsigned char))
#define TOPBIT (1<<(WIDTH-1))
unsigned char crcTable[256];

void init_crc(void);
unsigned char crc(unsigned char message[],unsigned char length);
