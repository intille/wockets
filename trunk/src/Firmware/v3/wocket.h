
#define MAX_COMMAND_SIZE 10
#define MAX_COMMAND_TIMER 255


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

/* Wockets Packet Format */
#define HEADER_PACKET 0x80
#define COMMAND_PREFIX 0b101

/* Reserved Wockets Commands Opcodes */

#define GET_BATTERY_LEVEL 			0b00000
#define GET_PACKET_COUNT  			0b00001
#define GET_SLEEP_MODE    			0b00010
#define SET_SLEEP_MODE    			0b00011
#define SET_LED           			0b00100
#define RESET_BLUETOOTH   			0b00101
#define GET_SENSOR_SENSITIVITY 		0b00110
#define SET_SENSOR_SENSITIVITY		0b00111
#define GET_CALIBRATION_VALUES		0b01000
#define SET_CALIBRATION_VALUES		0b01001
#define GET_TRANSMISSION_POWER		0b01010
#define SET_TRANSMISSION_POWER		0b01011
#define GET_SAMPLING_RATE			0b01100
#define SET_SAMPLING_RATE			0b01101
#define GET_DISCOVERABLE_STATUS		0b01110
#define SET_DISCOVERABLE_STATUS		0b01111
#define GET_TRANSMISSION_MODE		0b10000
#define SET_TRANSMISSION_MODE		0b10001
#define GET_ALIVE_TIMER				0b10010
#define	SET_ALIVE_TIMER				0b10011
#define GET_POWER_DOWN_TIMER		0b10100
#define SET_POWER_DOWN_TIMER		0b10101
#define RESET_WOCKET				0b10110
#define GET_CONFIGURATION_TIMER		0b10111
#define	SET_CONFIGURATION_TIMER		0b11000
#define GET_BAUD_RATE				0b11001
#define SET_BAUD_RATE				0b11010
#define ALIVE						0b11011
#define PAUSE						0b11100
#define RESUME						0b11101





/* Reserved Wockets Response Opcodes */

#define BATTERY_LEVEL_RESPONSE 		0b00000
#define PACKET_COUNT_RESPONSE 		0b00001
#define SLEEP_MODE_RESPONSE			0b00010
#define SENSOR_SENSITIVITY_RESPONSE	0b00011
#define CALIBRATION_VALUES_RESPONSE	0b00100
#define SAMPLING_RATE_RESPONSE		0b00101
#define POWER_DOWN_TIMER_RESPONSE	0b00111
#define BAUD_RATE_RESPONSE			0b01000
#define SUCCESS_RESPONSE			0b01001



/* MACROS */

/* Header Macros */
#define RESPONSE_HEADER(opcode) 	(0xc0|opcode)

/* Battery Level Macros */
#define m_BATTERY_LEVEL_BYTE0			RESPONSE_HEADER(BATTERY_LEVEL_RESPONSE)
#define m_BATTERY_LEVEL_BYTE1(level)		(level>>3)
#define m_BATTERY_LEVEL_BYTE2(level)		((level & 0x07)<<4)



/* Calibration Macros */
#define m_CALIBRATION_BYTE1_TO_X1G(aByte)  (((unsigned short)(aByte&0x7f))<<3) 
#define m_CALIBRATION_BYTE2_TO_X1G(aByte)  (((unsigned short)(aByte&0x70))>>4)


#define m_CALIBRATION_BYTE2_TO_XN1G(aByte)  (((unsigned short)(aByte&0x0f))<<6)
#define m_CALIBRATION_BYTE3_TO_XN1G(aByte)  (((unsigned short)(aByte&0x7e))>>1)



#define m_CALIBRATION_BYTE3_TO_Y1G(aByte)  (((unsigned short)(aByte&0x01))<<9) 
#define m_CALIBRATION_BYTE4_TO_Y1G(aByte)  (((unsigned short)(aByte&0x7f))<<2)
#define m_CALIBRATION_BYTE5_TO_Y1G(aByte)  (((unsigned short)(aByte&0x60))>>5)



#define m_CALIBRATION_BYTE5_TO_YN1G(aByte)  (((unsigned short)(aByte&0x1f))<<5)
#define m_CALIBRATION_BYTE6_TO_YN1G(aByte)  (((unsigned short)(aByte&0x7c))>>2)


#define m_CALIBRATION_BYTE6_TO_Z1G(aByte)  (((unsigned short)(aByte&0x03))<<8) 
#define m_CALIBRATION_BYTE7_TO_Z1G(aByte)  (((unsigned short)(aByte&0x7f))<<1)
#define m_CALIBRATION_BYTE8_TO_Z1G(aByte)  (((unsigned short)(aByte&0x40))>>6)


#define m_CALIBRATION_BYTE8_TO_ZN1G(aByte)  (((unsigned short)(aByte&0x3f))<<4)
#define m_CALIBRATION_BYTE9_TO_ZN1G(aByte)  (((unsigned short)(aByte&0x78))>>3)



#define m_CALIBRATION_BYTE0				RESPONSE_HEADER(CALIBRATION_VALUES_RESPONSE)
#define m_CALIBRATION_X1G_TO_BYTE1(x1g)	((x1g>>3)&0x7f)
#define m_CALIBRATION_X1G_TO_BYTE2(x1g)	((x1g<<4)&0x70)


#define m_CALIBRATION_XN1G_TO_BYTE2(xn1g)	((xn1g>>6)&0x0f)
#define m_CALIBRATION_XN1G_TO_BYTE3(xn1g)	((xn1g<<1)&0x7e)

#define m_CALIBRATION_Y1G_TO_BYTE3(y1g)	((y1g>>9) &0x01)
#define m_CALIBRATION_Y1G_TO_BYTE4(y1g)	((y1g>>2) & 0x7f)
#define m_CALIBRATION_Y1G_TO_BYTE5(y1g)	((y1g<<5) & 0x60)

#define m_CALIBRATION_YN1G_TO_BYTE5(yn1g)	((yn1g>>5) & 0x1f)
#define m_CALIBRATION_YN1G_TO_BYTE6(yn1g)	((yn1g<<2) & 0x7c)

#define m_CALIBRATION_Z1G_TO_BYTE6(z1g)	((z1g>>8) & 0x03)
#define m_CALIBRATION_Z1G_TO_BYTE7(z1g)	((z1g>>1) & 0x7f)
#define m_CALIBRATION_Z1G_TO_BYTE8(z1g)	((z1g<<6) & 0x40)

#define m_CALIBRATION_ZN1G_TO_BYTE8(zn1g)	((zn1g>>4) & 0x3f)
#define m_CALIBRATION_ZN1G_TO_BYTE9(zn1g)	((zn1g<<3) & 0x78)


#define m_SUCCESS_RESPONSE_BYTE1			RESPONSE_HEADER(SUCCESS_RESPONSE)


/* Baud Rate Macros */
#define m_BAUD_RATE_BYTE2_TO_BR(aByte)  (((unsigned short)(aByte&0x78))>>3) 
#define m_BAUD_RATE_BYTE0                       RESPONSE_HEADER(BAUD_RATE_RESPONSE)
#define m_BAUD_RATE_BYTE1(baud)         ((baud<<3)&0x78)




typedef struct{
	unsigned char byte1; //sync bit, 2 bits packet type, 3 bits sensitivity, 2 bits MSB X
	unsigned char byte2;	//0 bit, 7 X
	unsigned char byte3; // 0 bit, 1 LSB X, 6 MSB y
	unsigned char byte4; // 0 bit, 4 LSB y, 3 MSB z
	unsigned char byte5; // 0 bit, 7 LSB z
} wockets_uncompressed_packet;

unsigned char num_skipped_timer_interrupts;

void _wocket_initialize(void);
void _wocket_set_master_mode(void);
void _wocket_set_slave_mode(void);
unsigned char _wocket_is_master(void);
void _send_data(void);
void _receive_data(void);

unsigned short _wocket_read_baudrate(void);
void _wocket_write_baudrate(unsigned short baudrate);
wockets_uncompressed_packet _encode_packet(unsigned short x, unsigned short y, unsigned short z);
void _transmit_packet(wockets_uncompressed_packet packet);


//unsigned int min_shutdown_timer;
//unsigned char shutdown_timer;



