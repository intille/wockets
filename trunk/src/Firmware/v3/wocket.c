#include <avr/eeprom.h> 
#include "mcu_atmega.h"
#include "wocket.h"
#include <util/delay.h>

/* 
	Function Name: _wocket_get_baudrate
	Parameters: None
	
	Description: This function reads the baud rate from the eeprom, if not set, sets it to the default 38400
	Currently, the wockets support 9600, 19200, 28800, 38400 and 57600
	
*/

unsigned short _wocket_read_baudrate(void)
{
	unsigned short baudrate=eeprom_read_word((uint16_t *)((uint16_t)BAUD_RATE_ADDRESS));

	switch(baudrate)
	{
		case BAUD_9600:
			return ATMEGA_BAUD_9600;
		case BAUD_19200:
			return ATMEGA_BAUD_19200;
		case BAUD_28800:
			return ATMEGA_BAUD_28800;
		case BAUD_38400:
			return ATMEGA_BAUD_38400;
		case BAUD_57600:
			return ATMEGA_BAUD_57600;
		default:
			break;

	}
	eeprom_write_word((uint16_t *)BAUD_RATE_ADDRESS,BAUD_38400);
	return ATMEGA_BAUD_38400;
}

/* 
	Function Name: _wocket_set_baudrate
	Parameters: None
	
	Description: This function sets the baud rate for the wocket to one of the following values 9600, 19200, 28800, 38400 and 57600
	
*/
void _wocket_write_baudrate(unsigned short baudrate)
{
	if ((baudrate==BAUD_9600) || (baudrate==BAUD_19200) || (baudrate==BAUD_28800)|| (baudrate==BAUD_38400)|| (baudrate==BAUD_57600))
		eeprom_write_word((uint16_t *)BAUD_RATE_ADDRESS,baudrate);		
}

/* 
	Function Name: _wocket_intialize
	Parameters: None
	
	Description: This function initializes the wocket
	
*/
void _wocket_initialize(void)
{
	// Disable the watchdog timer. It has to be done at the beginning of the program.
	_atmega_disable_watchdog();
	_atmega_initialize(CPU_CLK_PRESCALAR_1024);
	num_skipped_timer_interrupts=10;//(F_CPU/1024)/PERFECT_SAMPLING_FREQUENCY;

	//read the baud rate from the eeprom
	unsigned short baudrate=_wocket_read_baudrate();
	
	//By default initialize the wocket to slave mode
	_wocket_set_slave_mode();	

//	F_CPU/PRESCALAR
	_atmega_adc_turn_on();
}

/* 
	Function Name:  _wocket_set_master_mode
	Parameters: None
	
	Description: This function sets the wocket into master mode
	
*/
void _wocket_set_master_mode(void)
{
	// Set the status of the master mode to true
	sbi(wocket_status, BIT4_MASTERSLAVE_STATUS);
}


/* 
	Function Name:  _wocket_set_slave_mode
	Parameters: None
	
	Description: This function sets the wocket into slave mode
	
*/
void _wocket_set_slave_mode(void)
{
	// Set the status of the master mode to true
	cbi(wocket_status, BIT4_MASTERSLAVE_STATUS);
}



/* 
	Function Name:  _wocket_is_master
	Parameters: None
	
	Description: Tests if the wocket is a master
	
*/
unsigned char _wocket_is_master(void)
{
	// Set the status of the master mode to true
	return ((wocket_status>>BIT4_MASTERSLAVE_STATUS) & 0x01);
}

wockets_uncompressed_packet _encode_packet(unsigned short x, unsigned short y, unsigned short z)
{
	wockets_uncompressed_packet packet;
	unsigned char sensitivity=0;
	packet.byte1=0;
	packet.byte2=0;
	packet.byte3=0;
	packet.byte4=0;
	packet.byte5=0;
	
	//set the sync bit,no compession, length and channel
	packet.byte1 =100; //0x80| ((unsigned char)((sensitivity&0x07)<<2)) | ((x>>8)& 0x03);
	packet.byte2 = 51;//((unsigned char) ((x>>1)&0x7f));
	packet.byte3 = 32;//((unsigned char) ((x<<6) &0x40)) | ((unsigned char) ((y>>4)&0x3f));
	packet.byte4 = 81;//((unsigned char) ((y<<3) &0x78)) | ((unsigned char) ((z>>7)&0x07));
	packet.byte5 = 22;//((unsigned char) (z&0x7f));

	return packet;

}

void _transmit_packet(wockets_uncompressed_packet packet)
{
	_bluetooth_transmit_uart0_byte(50);
	
	_bluetooth_transmit_uart0_byte(41);
	
	_bluetooth_transmit_uart0_byte(32);
	
	_bluetooth_transmit_uart0_byte(33);
	
	_bluetooth_transmit_uart0_byte(36);
	
}
