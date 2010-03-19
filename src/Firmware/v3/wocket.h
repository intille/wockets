

/* Wockets commands constants */

/* baud rates */
#define BAUD_1200 	0b0000
#define BAUD_2400 	0b0001
#define BAUD_4800 	0b0010
#define BAUD_9600 	0b0011
#define BAUD_19200 	0b0100
#define BAUD_28800	0b0101
#define BAUD_38400 	0b0110
#define BAUD_57600	0b0111
#define BAUD_115200	0b1000
#define BAUD_230000	0b1001
#define BAUD_460000	0b1010
#define BAUD_921000	0b1011

/* Reserved Wockets EEPROM Locations */

#define X1G_ADDRESS 0x00
#define X1NG_ADDRESS 0x02
#define Y1G_ADDRESS 0x04
#define Y1NG_ADDRESS 0x06
#define Z1G_ADDRESS 0x08
#define Z1NG_ADDRESS 0x0A
#define BAUD_RATE_ADDRESS 0x0C

#define PERFECT_SAMPLING_FREQUENCY 90

void _wocket_initialize(void);
void _wocket_set_master_mode(void);
void _wocket_set_slave_mode(void);
unsigned char _wocket_is_master(void);

unsigned short _wocket_read_baudrate(void);
void _wocket_write_baudrate(unsigned short baudrate);

unsigned char num_skipped_timer_interrupts;
//unsigned int min_shutdown_timer;
//unsigned char shutdown_timer;


typedef struct{
	char byte1; //sync bit, 2 bits packet type, 3 bits sensitivity, 2 bits MSB X
	char byte2;	//0 bit, 7 X
	char byte3; // 0 bit, 1 LSB X, 6 MSB y
	char byte4; // 0 bit, 4 LSB y, 3 MSB z
	char byte5; // 0 bit, 7 LSB z
} wockets_uncompressed_packet;
