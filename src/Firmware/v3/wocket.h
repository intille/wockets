typedef struct{
	unsigned char byte1;
	unsigned char byte2;
	unsigned char byte3;
	unsigned char byte4;
	unsigned char byte5;
	unsigned char byte6;
	unsigned char byte7;
	unsigned char byte8;
	unsigned char byte9;
	unsigned char byte10;
	unsigned char byte11;
	unsigned char byte12;
	unsigned char byte13;
	unsigned char byte14;
	unsigned char byte15;

} data_unit;





#define MAX_COMMAND_SIZE 10
#define MAX_COMMAND_TIMER 255


/* Wockets commands constants */

/* baud rates */
#define BAUD_9600 	1
#define BAUD_19200 	2
#define BAUD_38400 	0
#define BAUD_57600	3

/* Reserved Wockets EEPROM Locations */

#define X1G_ADDRESS 0x00
#define X1NG_ADDRESS 0x02
#define Y1G_ADDRESS 0x04
#define Y1NG_ADDRESS 0x06
#define Z1G_ADDRESS 0x08
#define Z1NG_ADDRESS 0x0A


/* Wockets Sensitivities */

#define _1_5_G 		0b000
#define _2_G 		0b001
#define _4_G		0b010
#define _6_G		0b011
#define _8_G		0b100
#define _INVALID_G	0b111


/* Wockets Transmission Modes */

#define _TM_Continuous	0b000
#define _TM_Burst_30	0b001
#define _TM_Burst_60	0b010
#define _TM_Burst_90	0b011
#define	_TM_Burst_120	0b100

/* Wockets Status Bits */
#define _STATUS_INITIALIZED 0


#define PERFECT_SAMPLING_FREQUENCY 90


/**  WOCKETS PDU FORMAT **/

/* PDU Types */

#define UNCOMPRESSED_PDU 0b00
#define COMMAND_PDU 0b01
#define RESPONSE_PDU 0b10
#define COMPRESSED_PDU 0b11



/* Macro for PDU Header */
#define m_HEADER(type) (0x80|(type<<5))

/* Macros for Uncompressed PDU */
#define m_UNCOMPRESSED_PDU_BYTE1(x) (m_HEADER(UNCOMPRESSED_PDU)|(x>>8))
#define m_UNCOMPRESSED_PDU_BYTE2(x) (0x7f & (x>>1))
#define m_UNCOMPRESSED_PDU_BYTE3(x,y) ((0x40 & (x<<6)) | (0x3f & (y>>4)))
#define m_UNCOMPRESSED_PDU_BYTE4(y,z) ((0x78 & (y<<3)) | (0x07 & (z>>7)))
#define m_UNCOMPRESSED_PDU_BYTE5(z) (0x7f & z)

/* Macros for compressed PDU */
#define m_COMPRESSED_PDU_BYTE1(x) 	(m_HEADER(COMPRESSED_PDU)|((x>>1)&0x1f))
#define m_COMPRESSED_PDU_BYTE2(x,y) (((x&0x01)<<6)|(y&0x3f))
#define m_COMPRESSED_PDU_BYTE3(z) 	(0x7e & (z<<1))

/* Macros for Command PDUs */

#define RESPONSE_HEADER(opcode) 	(0xc0|opcode)

#define HEADER_PACKET 0x80
#define COMMAND_PREFIX 0b101




/* Reserved Wockets Commands Opcodes */

#define GET_BT			0b00000
#define GET_BP 			0b00001
#define GET_PC 			0b00010
#define RST_BT 			0b00011
#define GET_SEN			0b00100
#define SET_SEN			0b00101
#define GET_CAL 		0b00110
#define SET_CAL			0b00111
#define GET_SR			0b01000
#define SET_SR			0b01001
#define GET_ALT			0b01010
#define SET_ALT			0b01011
#define GET_PDT			0b01100
#define SET_PDT			0b01101
#define RST_WKT			0b01110
#define ALIVE			0b01111
#define PAUSE			0b10000
#define RESUME			0b10001
#define GET_TM			0b10010
#define	SET_TM			0b10011
#define GET_BTCAL		0b10100
#define SET_BTCAL		0b10101
#define GET_HV			0b10110
#define GET_FV			0b10111

/* Macros for Wockets Commands */

/* SET_SEN Macros */
#define m_SET_SEN(aByte2) 	((aByte2>>3) & 0x07)

/* SET_SR Macros */
#define m_SET_SR(aByte2) 	(aByte2 & 0x7f)

/* SET_PDT Macros */
#define m_SET_PDT(aByte2) 	(aByte2 & 0x7f)

/* SET_TM Macros */
#define m_SET_TM(aByte2) 	((aByte2>>4) & 0x07)

/* SET_ALT Macros */
#define m_SET_ALT(aByte2) 	(aByte2 & 0x7f)

/* SET_TM Macros */
#define m_SET_TM(aByte2) 	((aByte2>>4) & 0x07)

/* SET_CAL Macros */
#define m_SET_CAL_x1g(aByte1,aByte2)  		(	(((unsigned short)(aByte1&0x7f))<<3) | 	(((unsigned short)(aByte2&0x70))>>4)	)
#define m_SET_CAL_xn1g(aByte2,aByte3)   	( 	(((unsigned short)(aByte2&0x0f))<<6) | 	(((unsigned short)(aByte3&0x7e))>>1)	)
#define m_SET_CAL_y1g(aByte3,aByte4,aByte5) ( 	(((unsigned short)(aByte3&0x01))<<9) |	(((unsigned short)(aByte4&0x7f))<<2) |	(((unsigned short)(aByte5&0x60))>>5)	)
#define m_SET_CAL_yn1g(aByte5,aByte6)  		( 	(((unsigned short)(aByte5&0x1f))<<5) | 	(((unsigned short)(aByte6&0x7c))>>2)	)
#define m_SET_CAL_z1g(aByte6,aByte7,aByte8) ( 	(((unsigned short)(aByte6&0x03))<<8) | 	(((unsigned short)(aByte7&0x7f))<<1) | 	(((unsigned short)(aByte8&0x40))>>6)	)
#define m_SET_CAL_zn1g(aByte8,aByte9)   	( 	(((unsigned short)(aByte8&0x3f))<<4) | 	(((unsigned short)(aByte9&0x78))>>3) 	)


/* SET_BTCAL Macros */
#define m_SET_BTCAL_100(aByte1,aByte2)  		(	(((unsigned short)(aByte1&0x7f))<<3) | 	(((unsigned short)(aByte2&0x70))>>4)	)
#define m_SET_BTCAL_80(aByte2,aByte3)   	( 	(((unsigned short)(aByte2&0x0f))<<6) | 	(((unsigned short)(aByte3&0x7e))>>1)	)
#define m_SET_BTCAL_60(aByte3,aByte4,aByte5) ( 	(((unsigned short)(aByte3&0x01))<<9) |	(((unsigned short)(aByte4&0x7f))<<2) |	(((unsigned short)(aByte5&0x60))>>5)	)
#define m_SET_BTCAL_40(aByte5,aByte6)  		( 	(((unsigned short)(aByte5&0x1f))<<5) | 	(((unsigned short)(aByte6&0x7c))>>2)	)
#define m_SET_BTCAL_20(aByte6,aByte7,aByte8) ( 	(((unsigned short)(aByte6&0x03))<<8) | 	(((unsigned short)(aByte7&0x7f))<<1) | 	(((unsigned short)(aByte8&0x40))>>6)	)
#define m_SET_BTCAL_10(aByte8,aByte9)   	( 	(((unsigned short)(aByte8&0x3f))<<4) | 	(((unsigned short)(aByte9&0x78))>>3) 	)


/* SET_SR Macros */
#define m_SET_SR(aByte2) (aByte2 & 0x7f)


/* Reserved Wockets Response Opcodes */

#define BL_RSP 		0b00000
#define BP_RSP 		0b00001
#define PC_RSP		0b00010
#define SENS_RSP	0b00011
#define CAL_RSP		0b00100
#define SR_RSP		0b00101
#define ALT_RSP		0b00110
#define PDT_RSP		0b00111
#define TM_RSP		0b01000
#define BTCAL_RSP 	0b01001
#define HV_RSP	 	0b01010
#define FV_RSP	 	0b01011
#define BC_RSP		0b01100

/* Macros for Wockets Responses */

/* BL_RSP Macros */
#define m_BL_RSP_BYTE0			RESPONSE_HEADER(BL_RSP)
#define m_BL_RSP_BYTE1(level)	(level>>3)
#define m_BL_RSP_BYTE2(level)	((level & 0x07)<<4)

/* BP_RSP Macros */

#define m_BP_RSP_BYTE0			RESPONSE_HEADER(BP_RSP)
#define m_BP_RSP_BYTE1(percent)	(percent&0x7f)




/* PC_RSP Macros */
#define m_PC_RSP_BYTE0			RESPONSE_HEADER(PC_RSP)
#define m_PC_RSP_BYTE1(count)		(count>>25)
#define m_PC_RSP_BYTE2(count)		((count>>18) & 0x7f)
#define m_PC_RSP_BYTE3(count)		((count>>11) & 0x7f)
#define m_PC_RSP_BYTE4(count)		((count>>4) & 0x7f)
#define m_PC_RSP_BYTE5(count)		((count & 0x0f)<<3)

/* SENS_RSP Macros */
#define m_SENS_RSP_BYTE0				RESPONSE_HEADER(SENS_RSP)
#define m_SENS_RSP_BYTE1(sensitivity)	((sensitivity & 0x07)<<4)

/* CAL_RSP Macros */

#define m_CAL_RSP_BYTE0					RESPONSE_HEADER(CAL_RSP)
#define m_CAL_RSP_BYTE1_x1g(x1g)		((x1g>>3)&0x7f)
#define m_CAL_RSP_BYTE2_x1g(x1g)		((x1g<<4)&0x70)
#define m_CAL_RSP_BYTE2_xn1g(xn1g)		((xn1g>>6)&0x0f)
#define m_CAL_RSP_BYTE3_xn1g(xn1g)		((xn1g<<1)&0x7e)
#define m_CAL_RSP_BYTE3_y1g(y1g)		((y1g>>9) &0x01)
#define m_CAL_RSP_BYTE4_y1g(y1g)		((y1g>>2) & 0x7f)
#define m_CAL_RSP_BYTE5_y1g(y1g)		((y1g<<5) & 0x60)
#define m_CAL_RSP_BYTE5_yn1g(yn1g)		((yn1g>>5) & 0x1f)
#define m_CAL_RSP_BYTE6_yn1g(yn1g)		((yn1g<<2) & 0x7c)
#define m_CAL_RSP_BYTE6_z1g(z1g)		((z1g>>8) & 0x03)
#define m_CAL_RSP_BYTE7_z1g(z1g)		((z1g>>1) & 0x7f)
#define m_CAL_RSP_BYTE8_z1g(z1g)		((z1g<<6) & 0x40)
#define m_CAL_RSP_BYTE8_zn1g(zn1g)		((zn1g>>4) & 0x3f)
#define m_CAL_RSP_BYTE9_zn1g(zn1g)		((zn1g<<3) & 0x78)

/* BTCAL_RSP Macros */

#define m_BTCAL_RSP_BYTE0					RESPONSE_HEADER(BTCAL_RSP)
#define m_BTCAL_RSP_BYTE1_100(percentile100)		((percentile100>>3)&0x7f)
#define m_BTCAL_RSP_BYTE2_100(percentile100)		((percentile100<<4)&0x70)
#define m_BTCAL_RSP_BYTE2_80(percentile80)		((percentile80>>6)&0x0f)
#define m_BTCAL_RSP_BYTE3_80(percentile80)		((percentile80<<1)&0x7e)
#define m_BTCAL_RSP_BYTE3_60(percentile60)		((percentile60>>9) &0x01)
#define m_BTCAL_RSP_BYTE4_60(percentile60)		((percentile60>>2) & 0x7f)
#define m_BTCAL_RSP_BYTE5_60(percentile60)		((percentile60<<5) & 0x60)
#define m_BTCAL_RSP_BYTE5_40(percentile40)		((percentile40>>5) & 0x1f)
#define m_BTCAL_RSP_BYTE6_40(percentile40)		((percentile40<<2) & 0x7c)
#define m_BTCAL_RSP_BYTE6_20(percentile20)		((percentile20>>8) & 0x03)
#define m_BTCAL_RSP_BYTE7_20(percentile20)		((percentile20>>1) & 0x7f)
#define m_BTCAL_RSP_BYTE8_20(percentile20)		((percentile20<<6) & 0x40)
#define m_BTCAL_RSP_BYTE8_10(percentile10)		((percentile10>>4) & 0x3f)
#define m_BTCAL_RSP_BYTE9_10(percentile10)		((percentile10<<3) & 0x78)

/* SR_RSP Macros */

#define m_SR_RSP_BYTE0			RESPONSE_HEADER(SR_RSP)
#define m_SR_RSP_BYTE1(sr)		(sr & 0x7f)

/* ALT_RSP Macros */

#define m_ALT_RSP_BYTE0				RESPONSE_HEADER(ALT_RSP)
#define m_ALT_RSP_BYTE1(timeout)	(timeout & 0x7f)

/* PDT_RSP Macros */

#define m_PDT_RSP_BYTE0				RESPONSE_HEADER(PDT_RSP)
#define m_PDT_RSP_BYTE1(timeout)	(timeout & 0x7f)


/* TM_RSP Macros */

#define m_TM_RSP_BYTE0				RESPONSE_HEADER(TM_RSP)
#define m_TM_RSP_BYTE1(mode)		((mode & 0x07)<<4)


/* HV_RSP Macros */

#define m_HV_RSP_BYTE0				RESPONSE_HEADER(HV_RSP)
#define m_HV_RSP_BYTE1(version)	(version & 0x7f)


/* FV_RSP Macros */

#define m_FV_RSP_BYTE0				RESPONSE_HEADER(FV_RSP)
#define m_FV_RSP_BYTE1(version)	(version & 0x7f)



/* BC_RSP Macros */
#define m_BC_RSP_BYTE0			RESPONSE_HEADER(BC_RSP)
#define m_BC_RSP_BYTE1(count)	((count>>7) &0x7f)
#define m_BC_RSP_BYTE2(count)	(count & 0x7f)


#define m_SUCCESS_RESPONSE_BYTE1			RESPONSE_HEADER(SUCCESS_RESPONSE)





#define BIT0_MASTERSLAVE_STATUS 0
#define BIT1_BURSTY_STATUS 1
#define BIT2_BIT3_BAUD_RATE 2



extern uint8_t EEMEM _NV_INITIALIZED;
extern uint8_t EEMEM _NV_STATUS_BYTE;
extern uint8_t EEMEM _NV_SAMPLING_RATE;
extern uint8_t EEMEM _NV_DEBUG;
extern unsigned char _INITIALIZED;
extern unsigned char _STATUS_BYTE;
extern unsigned char _SAMPLING_RATE;
extern unsigned char _wTCNT2_reps;
extern unsigned char _wTCNT2;
extern unsigned char _wTCNT2_last;
extern unsigned char _wTM;
extern unsigned long _wPC;
extern unsigned long _wShutdownTimer;
extern unsigned long _DEFAULT_SHUTDOWN;
extern unsigned char _wPDT;

typedef struct{
	unsigned char byte1; //sync bit, 2 bits packet type, 3 bits sensitivity, 2 bits MSB X
	unsigned char byte2;	//0 bit, 7 X
	unsigned char byte3; // 0 bit, 1 LSB X, 6 MSB y
	unsigned char byte4; // 0 bit, 4 LSB y, 3 MSB z
	unsigned char byte5; // 0 bit, 7 LSB z
} wockets_uncompressed_packet;

unsigned char num_skipped_timer_interrupts;
unsigned char wocket_status;
//unsigned short xs[256];
//unsigned short ys[256];
//unsigned short zs[256];
unsigned short scounter;


/*
extern data_unit data1[100];
extern data_unit data2[100];
extern data_unit data3[100];
extern data_unit data4[100];
extern data_unit data5[100];
extern data_unit data6[100];
extern data_unit data7[50];*/

//extern unsigned short xs[3000];
//extern unsigned short ys[3000];
//extern unsigned short zs[3000];
extern data_unit data[750];
extern unsigned short dataIndex;
extern unsigned char dataSubindex;

extern unsigned short *xsp;
extern unsigned short *ysp;
extern unsigned short *zsp;

#define m_SET_X(pdata,x,index) switch(index){\
									case 0: pdata.byte1=(x>>2);pdata.byte2=((x<<6)&0xc0);break;\
									case 1: pdata.byte4|=(x>>8);pdata.byte5=(x&0xff);break;\
									case 2: pdata.byte8|=(x>>6);pdata.byte9=((x<<2)&0xfc);break;\
									case 3: pdata.byte12|=(x>>4);pdata.byte13=((x<<4)&0xf0);break;}
#define m_SET_Y(pdata,y,index) switch(index){\
									case 0: pdata.byte2|=(y>>4);pdata.byte3=((y<<4)&0xf0);break;\
									case 1: pdata.byte6=(y>>2);pdata.byte7=((y<<6)&0xc0);break;\
									case 2: pdata.byte9|=(y>>8);pdata.byte10=(y&0xff);break;\
									case 3: pdata.byte13|=(y>>6);pdata.byte14=((y<<2)&0xfc);break;}
#define m_SET_Z(pdata,z,index) switch(index){\
									case 0: pdata.byte3|=(z>>6);pdata.byte4=((z<<2)&0xfc);break;\
									case 1: pdata.byte7|=(z>>4);pdata.byte8=((z<<4)&0xf0);break;\
									case 2: pdata.byte11=(z>>2);pdata.byte12=((z<<6)&0xc0);break;\
									case 3: pdata.byte14|=(z>>8);pdata.byte15=(z&0xff);break;}


#define m_GET_X(x,byte1,byte2,index) switch(index){\
									case 0: x=((byte1&0xff)<<2)|((byte2&0xc0)>>6); break;\
									case 1: x=((byte1&0x03)<<8)|(byte2&0xff);break;\
									case 2: x=((byte1&0x0f)<<6)|((byte2 &0xfc)>>2);break;\
									case 3: x=((byte1&0x3f)<<4)|((byte2&0xf0)>>4);break;}

#define m_GET_Y(y,byte1,byte2,index) switch(index){\
									case 0: y=((byte1&0x3f)<<4)|(byte2>>4); break;\
									case 1: y=(byte1<<2)|(byte2>>6);break;\
									case 2: y=((byte1&0x03)<<8)|byte2;break;\
									case 3: y=((byte1&0x0f)<<6)|(byte2>>2);break;} 


#define m_GET_Z(z,byte1,byte2,index) switch(index){\
									case 0: z=((byte1&0x0f)<<6)|(byte2>>2); break;\
									case 1: z=((byte1&0x3f)<<4)|(byte2>>4);break;\
									case 2: z=(byte1<<2)|(byte2>>6);break;\
									case 3: z=((byte1&0x03)<<8)|byte2;break;}

void _wocket_initialize(void);
void _wocket_set_master_mode(void);
void _wocket_set_slave_mode(void);
unsigned char _wocket_is_master(void);


unsigned char _wocket_is_flag_set(unsigned char flag);
void _wocket_reset_flag(unsigned char flag);
void _wocket_set_flag(unsigned char flag);

void _send_data(void);
void _receive_data(void);
void _send_batch_count(unsigned short count);
void _send_data_bufferred(void);

unsigned char _wocket_get_baudrate(void);
void _wocket_set_baudrate(unsigned char baudrate);
wockets_uncompressed_packet _encode_packet(unsigned short x, unsigned short y, unsigned short z);
void _transmit_packet(wockets_uncompressed_packet packet);




//unsigned int min_shutdown_timer;
//unsigned char shutdown_timer;



