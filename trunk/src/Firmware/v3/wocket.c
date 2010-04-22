#include <avr/eeprom.h> 
#include "mcu_atmega.h"
#include "wocket.h"
#include <util/delay.h>


//A buffer to store commands from the phone
unsigned char aBuffer[MAX_COMMAND_SIZE];

//counts how many bytes received for a command
unsigned char command_counter=0;
//stores the length of a command
unsigned char command_length=0;
unsigned char opcode;
unsigned int command_timer=0;
unsigned char processed_counter=0;
unsigned short address=0xffff;
unsigned char response_length=0;
unsigned char paused=0;
unsigned int alive_timer=0;
unsigned short word=0;

unsigned short x=0;
unsigned short y=0;
unsigned short z=0;



unsigned char _wocket_get_baudrate(void)
{
	return ((wocket_status>>BIT2_BIT3_BAUD_RATE) & 0x03);
}

void _wocket_set_baudrate(unsigned char baudrate)
{
	if ((baudrate!=BAUD_9600)&&(baudrate!=BAUD_19200)&&(baudrate!=BAUD_38400)&&(baudrate!=BAUD_57600))
		return;

	wocket_status=(wocket_status & 0xF3) | (baudrate<< BIT2_BIT3_BAUD_RATE);		
	_wocket_write_status(wocket_status);
}

/* 
	Function Name: _wocket_get_baudrate
	Parameters: None
	
	Description: This function reads the baud rate from the eeprom, if not set, sets it to the default 38400
	Currently, the wockets support 9600, 19200, 28800, 38400 and 57600
	
*/

unsigned char _wocket_read_status(void)
{
	return eeprom_read_byte((uint8_t *)((uint8_t)WOCKET_STATUS_ADDRESS));
}

/* 
	Function Name: _wocket_set_baudrate
	Parameters: None
	
	Description: This function sets the baud rate for the wocket to one of the following values 9600, 19200, 28800, 38400 and 57600
	
*/
void _wocket_write_status(unsigned char status)
{
		eeprom_write_byte((uint8_t *)WOCKET_STATUS_ADDRESS,status);	
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
	//unsigned short baudrate=_wocket_read_baudrate();
	
	//read wocket status byte
	wocket_status=_wocket_read_status();


	//	F_CPU/PRESCALAR
	//_atmega_adc_turn_on();
}

/* 
	Function Name:  _wocket_set_master_mode
	Parameters: None
	
	Description: This function sets the wocket into master mode
	
*/
void _wocket_set_master_mode(void)
{
	// Set the status of the master mode to true
	sbi(wocket_status, BIT0_MASTERSLAVE_STATUS);
}


/* 
	Function Name:  _wocket_set_slave_mode
	Parameters: None
	
	Description: This function sets the wocket into slave mode
	
*/
void _wocket_set_slave_mode(void)
{
	// Set the status of the master mode to true
	cbi(wocket_status, BIT0_MASTERSLAVE_STATUS);
}



/* 
	Function Name:  _wocket_is_master
	Parameters: None
	
	Description: Tests if the wocket is a master
	
*/
unsigned char _wocket_is_master(void)
{
	// Set the status of the master mode to true
	return ((wocket_status>>BIT0_MASTERSLAVE_STATUS) & 0x01);
}



/* 
	Function Name:  _wocket_set_bursty_mode
	Parameters: None
	
	Description: This function sets the wocket into bursty mode
	
*/
void _wocket_set_bursty_mode(void)
{
	// Set the status of the master mode to true
	sbi(wocket_status, BIT1_BURSTY_STATUS);
}


/* 
	Function Name:  _wocket_set_continuous_mode
	Parameters: None
	
	Description: This function sets the wocket into continuous mode
	
*/
void _wocket_set_continuous_mode(void)
{
	// Set the status of the master mode to true
	cbi(wocket_status, BIT1_BURSTY_STATUS);
}



/* 
	Function Name:  _wocket_is_bursty
	Parameters: None
	
	Description: Tests if the wocket is a master
	
*/
unsigned char _wocket_is_bursty(void)
{
	// Check if the wocket is in bursty mode
	return ((wocket_status>>BIT1_BURSTY_STATUS) & 0x01);
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
	packet.byte1 =0x80| ((unsigned char)((sensitivity&0x07)<<2)) | ((x>>8)& 0x03);
	packet.byte2 = ((unsigned char) ((x>>1)&0x7f));
	packet.byte3 = ((unsigned char) ((x<<6) &0x40)) | ((unsigned char) ((y>>4)&0x3f));
	packet.byte4 = ((unsigned char) ((y<<3) &0x78)) | ((unsigned char) ((z>>7)&0x07));
	packet.byte5 = ((unsigned char) (z&0x7f));

	return packet;

}

void _transmit_packet(wockets_uncompressed_packet packet)
{
	_bluetooth_transmit_uart0_byte(packet.byte1);
	
	_bluetooth_transmit_uart0_byte(packet.byte2);
	
	_bluetooth_transmit_uart0_byte(packet.byte3);
	
	_bluetooth_transmit_uart0_byte(packet.byte4);
	
	_bluetooth_transmit_uart0_byte(packet.byte5);
	
}


void _send_packet_count(unsigned short count)
{
 
    aBuffer[0]=m_PACKET_COUNT_BYTE0;
    aBuffer[1]=m_PACKET_COUNT_BYTE1(count);
    aBuffer[2]=m_PACKET_COUNT_BYTE2(count);
	aBuffer[3]=m_PACKET_COUNT_BYTE3(count);
	for (int i=0;(i<4);i++)                                                                                       
       	_bluetooth_transmit_uart0_byte(aBuffer[i]); 
 
}
void _send_data_bufferred(void)
{
	
		if (paused==0)
		{
 			alive_timer++;                                  
            if (alive_timer>=2730) //if no acks for approx 30 seconds, reset radio
            {
            	//_atmega_reset();
				_bluetooth_reset();
            	alive_timer=0;                                  
            }
			//unsigned short x=_atmega_a2dConvert10bit(ADC3);
			//unsigned short y=_atmega_a2dConvert10bit(ADC2);
			//unsigned short z=_atmega_a2dConvert10bit(ADC1);

			for (int i=0;(i<2400);i++){
				_transmit_packet(_encode_packet(x++,y++,z++));
			/*	if ((i==2400))
					for (int j=0;(j<100);j++)
						_delay_ms(5);*/
				}
			if (x>1023)
			{
				x=0;
				y=0;
				z=0;
			}
			//}
		}
}




void _send_data(void)
{	
	if (paused==0)
	{
 		alive_timer++;                                  
        if (alive_timer>=2730) //if no acks for approx 30 seconds, reset radio
        {
           //	_atmega_reset();
		   _bluetooth_reset();
           	alive_timer=0;                                  
        }
		unsigned short x=_atmega_a2dConvert10bit(ADC3);
		unsigned short y=_atmega_a2dConvert10bit(ADC2);
		unsigned short z=_atmega_a2dConvert10bit(ADC1);
		_transmit_packet(_encode_packet(x,y,z));				
	}
}
void _receive_data(void)
{
	unsigned char aByte;

	// Attempt to receive a byte only if no command is being received or a partial comman has been received
	if ( ((command_counter==0)||(command_counter<command_length))  && (_bluetooth_receive_uart0_byte(&aByte)) )
    {
		aBuffer[command_counter++]=aByte;
		
		if ((aByte>>5)==COMMAND_PREFIX)
    	{
        	opcode=aByte&0x1f;                                              
        	switch (opcode)
			{
            	case (unsigned char)GET_BATTERY_LEVEL:
                case (unsigned char)GET_PACKET_COUNT:
                case (unsigned char)GET_SENSOR_SENSITIVITY:
                case (unsigned char)GET_CALIBRATION_VALUES:
                case (unsigned char)GET_SAMPLING_RATE:
                case (unsigned char)GET_ALIVE_TIMER:
                case (unsigned char)GET_POWER_DOWN_TIMER:
                case (unsigned char)RESET_WOCKET:
                case (unsigned char)GET_BAUD_RATE:
                case (unsigned char)ALIVE:                      
                case (unsigned char)PAUSE:
                case (unsigned char)RESUME:
                	command_length=1;
                    break;
                case (unsigned char)SET_LED:
                case (unsigned char)SET_SENSOR_SENSITIVITY:            
                case (unsigned char)SET_SAMPLING_RATE:
                case (unsigned char)SET_ALIVE_TIMER:
                case (unsigned char)SET_POWER_DOWN_TIMER:
                case (unsigned char)SET_BAUD_RATE:                                              
                     command_length=2;
                     break;
                case (unsigned char)SET_CALIBRATION_VALUES:
                      command_length=10;                                                              
                      break;                                                          
    		}
    		command_counter=1;
    		command_timer=0;
    		processed_counter=0;                                            
    		address=0xffff;
    		response_length=0;
		}

	}

	// increment timer as long as the command is still being received
    if (command_counter>0)
		command_timer++;


 	//if all command is received, start processing it
    if ((command_counter>0) && (command_counter==command_length))
    {                                       
            switch (opcode)
            {
                    case (unsigned char)PAUSE:                                                      
                            paused=1;
                            processed_counter=command_counter;                                                      
                            break;
                    case (unsigned char)RESUME:                                                     
                            paused=0;
                            processed_counter=command_counter;                                                      
                            break;
                    //reset alive timer if it is alive
                    case (unsigned char)ALIVE:                                                      
                            alive_timer=0;
                            processed_counter=command_counter; 
				
                            break;
                    //setup battery buffer
                case (unsigned char) GET_BATTERY_LEVEL:             
                            word=_atmega_a2dConvert10bit(ADC4);
                            aBuffer[0]=m_BATTERY_LEVEL_BYTE0;
                            aBuffer[1]=m_BATTERY_LEVEL_BYTE1(word);
                            aBuffer[2]=m_BATTERY_LEVEL_BYTE2(word);
                            processed_counter=command_counter;
                            response_length=3;
							/*if (_is_greenled_on())
								_greenled_turn_off();
							else
								_greenled_turn_on();                                                                              */
                            break;
                    case (unsigned char) SET_BAUD_RATE:
                           /* if (_atmega_a2dConvert10bit(ADC4)<350)
                                    break;
                            else if (eeprom_is_ready())
                            {
                                    word=m_BAUD_RATE_BYTE2_TO_BR(aBuffer[1]);
                                    eeprom_write_word((uint16_t *)BAUD_RATE_ADDRESS,word);
                                    processed_counter=command_counter;
                            }*/
                            break;
                    case (unsigned char) GET_BAUD_RATE:
                            /*word=eeprom_read_word((uint16_t *)((uint16_t)BAUD_RATE_ADDRESS));
                            aBuffer[0]=m_BAUD_RATE_BYTE0;
                            aBuffer[1]=m_BAUD_RATE_BYTE1(word);                             
                            processed_counter=command_counter;
                            response_length=2; */
                            break;
                    case (unsigned char) SET_CALIBRATION_VALUES:                                                                    
                            if (eeprom_is_ready())
                            {
                                    //do nothing if battery is low
                                    if (_atmega_a2dConvert10bit(ADC4)<350)
                                            break;
                                    else
                                    {       switch(address)
                                            {
                                                    case X1G_ADDRESS:
                                                            word=m_CALIBRATION_BYTE2_TO_XN1G(aBuffer[2]) | m_CALIBRATION_BYTE3_TO_XN1G(aBuffer[3]);
                                                            address=X1NG_ADDRESS;
                                                            break;
                                                    case X1NG_ADDRESS:
                                                            word=m_CALIBRATION_BYTE3_TO_Y1G(aBuffer[3])|m_CALIBRATION_BYTE4_TO_Y1G(aBuffer[4])|m_CALIBRATION_BYTE5_TO_Y1G(aBuffer[5]);
                                                            address=Y1G_ADDRESS;
                                                            break;
                                                    case Y1G_ADDRESS:
                                                            word=m_CALIBRATION_BYTE5_TO_YN1G(aBuffer[5])|m_CALIBRATION_BYTE6_TO_YN1G(aBuffer[6]);//(((unsigned short)(aBuffer[5]&0x1f))<<5) | (((unsigned short)(aBuffer[6]&0x7c))>>2);
                                                            address=Y1NG_ADDRESS;
                                                            break;
                                                    case Y1NG_ADDRESS:
                                                            word= m_CALIBRATION_BYTE6_TO_Z1G(aBuffer[6]) | m_CALIBRATION_BYTE7_TO_Z1G(aBuffer[7]) | m_CALIBRATION_BYTE8_TO_Z1G(aBuffer[8]) ;//(((unsigned short)(aBuffer[6]&0x03))<<8) | (((unsigned short)(aBuffer[7]&0x7f))<<1) | (((unsigned short)(aBuffer[8]&0x40))>>6);
                                                            address=Z1G_ADDRESS;
                                                            break;
                                                    case Z1G_ADDRESS:
                                                            word= m_CALIBRATION_BYTE8_TO_ZN1G(aBuffer[8]) |m_CALIBRATION_BYTE9_TO_ZN1G(aBuffer[9]);
                                                            address=Z1NG_ADDRESS;
                                                            processed_counter=command_counter;
                                                            break;
                                                    default:
                                                            word=m_CALIBRATION_BYTE1_TO_X1G(aBuffer[1])| m_CALIBRATION_BYTE2_TO_X1G(aBuffer[2]);                                                                                                                                            
                                                            address=X1G_ADDRESS;
                                                            break;                                                                                                                                                                          
                                            }
                                            eeprom_write_word((uint16_t *)address,word);
                                    }                                                                                                                                                                                                                                                       
                                                                                                                                    
                            }                                                                                                                       
                            //enable global interrupts
                            break;
                    case (unsigned char) GET_CALIBRATION_VALUES:    
                                                                    
                            if (eeprom_is_ready())
                            {                                                               
                                    //do nothing if battery is low
                                    if (_atmega_a2dConvert10bit(ADC4)<350)
                                            break;
                                    else                                                            
                                    {
                                            switch(address)
                                            {
                                                    case X1G_ADDRESS:
                                                            aBuffer[1]= m_CALIBRATION_X1G_TO_BYTE1(word);                                                                   
                                                            aBuffer[2]= m_CALIBRATION_X1G_TO_BYTE2(word);
                                                            address=X1NG_ADDRESS;
                                                            break;
                                                    case X1NG_ADDRESS:
                                                            aBuffer[2]|= m_CALIBRATION_XN1G_TO_BYTE2(word);
                                                            aBuffer[3] =m_CALIBRATION_XN1G_TO_BYTE3(word);
                                                            address=Y1G_ADDRESS;
                                                            break;
                                                    case Y1G_ADDRESS:
                                                            aBuffer[3]|= m_CALIBRATION_Y1G_TO_BYTE3(word);
                                                            aBuffer[4] = m_CALIBRATION_Y1G_TO_BYTE4(word);
                                                            aBuffer[5] =  m_CALIBRATION_Y1G_TO_BYTE5(word);
                                                            address=Y1NG_ADDRESS;
                                                            break;
                                                    case Y1NG_ADDRESS:
                                                            aBuffer[5]|= m_CALIBRATION_YN1G_TO_BYTE5(word);
                                                            aBuffer[6] = m_CALIBRATION_YN1G_TO_BYTE6(word);
                                                            address=Z1G_ADDRESS;
                                                            break;
                                                    case Z1G_ADDRESS:
                                                            aBuffer[6] |= m_CALIBRATION_Z1G_TO_BYTE6(word);
                                                            aBuffer[7] = m_CALIBRATION_Z1G_TO_BYTE7(word);
                                                            aBuffer[8] = m_CALIBRATION_Z1G_TO_BYTE8(word);
                                                            address=Z1NG_ADDRESS;
                                                            break;
                                                    case Z1NG_ADDRESS:
                                                            aBuffer[8] |= m_CALIBRATION_ZN1G_TO_BYTE8(word);
                                                            aBuffer[9] = m_CALIBRATION_ZN1G_TO_BYTE9(word);
                                                            processed_counter=command_counter;
                                                            response_length=10;
                                                            break;
                                                    default:
                                                            aBuffer[0]=m_CALIBRATION_BYTE0; 
                                                            address=X1G_ADDRESS;
                                                            break;                                                                                                                                                                          
                                            }
                                            word=eeprom_read_word((uint16_t *)((uint16_t)address));
                                    }                                                                                                                                                                               
                            
                            }                                                       
                            break;                                  
                    default:        
                            break;

            }

            if (processed_counter==command_counter)
			{                                        
                            
                    for (int i=0;(i<response_length);i++)                                                                                       
                     	_bluetooth_transmit_uart0_byte(aBuffer[i]);                                                                                                                                                   
                    command_length=0;
                    command_counter=0;
                    command_timer=0;
                    processed_counter=0;                                            
                    address=0xffff;
                    response_length=0;
                    
            }
    } //if command timed out
    else if (command_timer>=MAX_COMMAND_TIMER)
    {                            
            command_length=0;
            command_counter=0;
            command_timer=0;
            processed_counter=0;                            
            address=0xffff;
            response_length=0;

    }

}
