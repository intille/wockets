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


#define _WOCKET_INITIALIZED 0x25

uint8_t EEMEM _NV_INITIALIZED;
uint8_t EEMEM _NV_STATUS_BYTE;
uint8_t EEMEM _NV_SAMPLING_RATE;

unsigned char _INITIALIZED=0;
unsigned char _STATUS_BYTE=0;
unsigned char _SAMPLING_RATE=90;
unsigned char _wTCNT2_reps=1;
unsigned char _wTCNT2=0;
unsigned char _wTCNT2_last=0;
unsigned char _wTM=_TM_Continuous;

/* 
	Function Name: _wocket_set_baudrate
	Parameters: None
	
	Description: This function sets the baud rate for the wocket to one of the following values 9600, 19200, 28800, 38400 and 57600
	
*/


void _wocket_initialize_timer2_interrupt(void)
{
	unsigned short ticks=(unsigned short) ((F_CPU/1024)/_SAMPLING_RATE);
	if (ticks>256)
	{
		_wTCNT2=0;
		_wTCNT2_reps=(ticks/256)+1;
		_wTCNT2_last=255-(ticks%256);
	}else
	{
		_wTCNT2=255-ticks;
		_wTCNT2_reps=0;
		_wTCNT2_last=255;
	}
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
;

	
	/* Blink yellow for 5 seconds if battery not fully charged */
	unsigned short battery=_atmega_a2dConvert10bit(ADC4);
	if (battery<700)
	{
		for (int i=0;(i<5);i++){
			_yellowled_turn_on();		
			for(int i=0;(i<200);i++)
				_delay_ms(5);
			_yellowled_turn_off();
		}
	}

	/* Load the status byte from the EEPROM if it fails turn on the yellow led for 5 seconds then 
	   shutdown */
	if (battery>100)
	{
		_INITIALIZED=eeprom_read_byte(&_NV_INITIALIZED);		
	}
	else
	{
		_yellowled_turn_on();		
		for(int i=0;(i<1000);i++)
			_delay_ms(5);
		_yellowled_turn_off();
		_atmega_finalize();
		return;
	}
	
	/* If the wocket has been initialized */
	if (_INITIALIZED==_WOCKET_INITIALIZED)
	{
		// Read the sampling rate from the EEPROM
		if (battery>300)
		{
			_SAMPLING_RATE=eeprom_read_byte(&_NV_SAMPLING_RATE);
			_STATUS_BYTE=eeprom_read_byte(&_NV_STATUS_BYTE);
		}

		// Load the transmission mode		
		_wTM=(_STATUS_BYTE>>1)&0x07;		
	}
	/* If the wocket has never been initialized, write the default settings and blink green for 5 seconds */
	else
	{

		// Set the sampling rate to 90Hz
		_SAMPLING_RATE=90;
		_wTM=_TM_Continuous;
	
		// Write the sampling rate to the EEPROM
		if (battery>300)
		{
			eeprom_write_byte(&_NV_SAMPLING_RATE,_SAMPLING_RATE);
			eeprom_write_byte(&_NV_STATUS_BYTE,0x00);
		}

		// Set the initialized flag in the status byte
		_INITIALIZED=_WOCKET_INITIALIZED;

		// Write the status byte to the EEPROM		
		eeprom_write_byte(&_NV_INITIALIZED,_INITIALIZED);
				
		// Blink green for 5 seconds	
		_greenled_turn_on();		
		for(int i=0;(i<1000);i++)
			_delay_ms(5);
		_greenled_turn_off();		
	}

	/* Set the overflow interrupt timer */
	unsigned char _MAX_SAMPLING_RATE=0;
	switch(_wTM)
	{
		case _TM_Continuous:	
			_MAX_SAMPLING_RATE=126;
			break;			
		case _TM_Burst_30:
			_MAX_SAMPLING_RATE=80;		
			break;
		case _TM_Burst_60:
			_MAX_SAMPLING_RATE=40;		
			break;
		case _TM_Burst_90:
			_MAX_SAMPLING_RATE=30;		
			break;
		case _TM_Burst_120:
			_MAX_SAMPLING_RATE=20;		
			break;
		default:
			break;
	}	
	if (_SAMPLING_RATE>_MAX_SAMPLING_RATE)
	{
		_yellowled_turn_on();		
		for(int i=0;(i<1000);i++)
			_delay_ms(5);
		_yellowled_turn_off();
		_atmega_finalize();
		return;
	}

	// Calculate the timer variables used to sample at the right frequency
	_wocket_initialize_timer2_interrupt();
	
	
     /* Enable Timer 2 */
     _atmega_enable_timer2(CPU_CLK_PRESCALAR_1024);

}

void _wocket_set_flag(unsigned char flag)
{
	sbi(_STATUS_BYTE, flag);
}


void _wocket_reset_flag(unsigned char flag)
{
		cbi(_STATUS_BYTE, flag);
}



unsigned char _wocket_is_flag_set(unsigned char flag)
{	
	return ((_STATUS_BYTE>>flag) & 0x01);
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


void _send_packet_count(unsigned long count)
{
 
    aBuffer[0]=m_PACKET_COUNT_BYTE0;
    aBuffer[1]=m_PACKET_COUNT_BYTE1(count);
    aBuffer[2]=m_PACKET_COUNT_BYTE2(count);
	aBuffer[3]=m_PACKET_COUNT_BYTE3(count);
	aBuffer[4]=m_PACKET_COUNT_BYTE3(count);
	aBuffer[5]=m_PACKET_COUNT_BYTE3(count);
	for (int i=0;(i<6);i++)                                                                                       
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

			unsigned mycounter=0;
			for (int i=0;(i<2400);i++){
				//_transmit_packet(_encode_packet(x++,y++,z++));
				_transmit_packet(_encode_packet(xs[mycounter],ys[mycounter],zs[mycounter]));
				mycounter++;
				if (mycounter>255)
					mycounter=0;
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
            	case (unsigned char)GET_BT:
                case (unsigned char)GET_BP:
                case (unsigned char)GET_PC:
                case (unsigned char)RST_BT:
                case (unsigned char)GET_SEN:
                case (unsigned char)GET_CAL:
                case (unsigned char)GET_SR:
                case (unsigned char)GET_ALT:
                case (unsigned char)GET_PDT:
                case (unsigned char)RST_WKT:                      
                case (unsigned char)ALIVE:
                case (unsigned char)PAUSE:
				case (unsigned char)RESUME:
				case (unsigned char)GET_TM:
                	command_length=1;
                    break;
                case (unsigned char)SET_SEN:
                case (unsigned char)SET_SR:            
                case (unsigned char)SET_ALT:
                case (unsigned char)SET_PDT:
                case (unsigned char)SET_TM:                
                     command_length=2;
                     break;
                case (unsigned char)SET_CAL:
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
                case (unsigned char) GET_BT:             
                            word=_atmega_a2dConvert10bit(ADC4);
                            aBuffer[0]=m_BL_RSP_BYTE0;
                            aBuffer[1]=m_BL_RSP_BYTE1(word);
                            aBuffer[2]=m_BL_RSP_BYTE2(word);
                            processed_counter=command_counter;
                            response_length=3;		                                                                          
                            break;
               
                    case (unsigned char) SET_CAL:                                                                    
                            if (eeprom_is_ready())
                            {
                                    //do nothing if battery is low
                                    if (_atmega_a2dConvert10bit(ADC4)<350)
                                            break;
                                    else
                                    {       switch(address)
                                            {
                                                    case X1G_ADDRESS:
															word=m_SET_CAL_xn1g(aBuffer[2],aBuffer[3]);														                                                            
                                                            address=X1NG_ADDRESS;
                                                            break;
                                                    case X1NG_ADDRESS:
															word=m_SET_CAL_y1g(aBuffer[3],aBuffer[4],aBuffer[5]);                                                            
                                                            address=Y1G_ADDRESS;
                                                            break;
                                                    case Y1G_ADDRESS:
															word= m_SET_CAL_yn1g(aBuffer[5],aBuffer[6]);                                                            
                                                            address=Y1NG_ADDRESS;
                                                            break;
                                                    case Y1NG_ADDRESS:
                                                            word= m_SET_CAL_z1g(aBuffer[6],aBuffer[7],aBuffer[8]);
                                                            address=Z1G_ADDRESS;
                                                            break;
                                                    case Z1G_ADDRESS:
															word=m_SET_CAL_zn1g(aBuffer[8],aBuffer[8]);                                                            
                                                            address=Z1NG_ADDRESS;
                                                            processed_counter=command_counter;
                                                            break;
                                                    default:
															word=m_SET_CAL_x1g(aBuffer[1],aBuffer[2]);                                                            
                                                            address=X1G_ADDRESS;
                                                            break;                                                                                                                                                                          
                                            }
                                            eeprom_write_word((uint16_t *)address,word);
                                    }                                                                                                                                                                                                                                                       
                                                                                                                                    
                            }                                                                                                                       
                            //enable global interrupts
                            break;
                    case (unsigned char) GET_CAL:    

							/* Firmware response are written without compromising the sampling rate and
							therefore may have some delay in processing */
							                                                                    
                            if (eeprom_is_ready())
                            {                                                               
                                    // Don't read from the eeprom if the battery is too low
                                    if (_atmega_a2dConvert10bit(ADC4)<350)
                                            break;
                                    else                                                            
                                    {
                                            switch(address)
                                            {
                                                    case X1G_ADDRESS:
                                                            aBuffer[1]= m_CAL_RSP_BYTE1_x1g(word);                                                                   
                                                            aBuffer[2]= m_CAL_RSP_BYTE2_x1g(word);
                                                            address=X1NG_ADDRESS;
                                                            break;
                                                    case X1NG_ADDRESS:
                                                            aBuffer[2]|= m_CAL_RSP_BYTE2_xn1g(word);
                                                            aBuffer[3] = m_CAL_RSP_BYTE3_xn1g(word);
                                                            address=Y1G_ADDRESS;
                                                            break;
                                                    case Y1G_ADDRESS:
                                                            aBuffer[3]|= m_CAL_RSP_BYTE3_y1g(word);
                                                            aBuffer[4] = m_CAL_RSP_BYTE4_y1g(word);
                                                            aBuffer[5] = m_CAL_RSP_BYTE5_y1g(word);
                                                            address=Y1NG_ADDRESS;
                                                            break;
                                                    case Y1NG_ADDRESS:
                                                            aBuffer[5]|= m_CAL_RSP_BYTE5_yn1g(word);
                                                            aBuffer[6] = m_CAL_RSP_BYTE6_yn1g(word);
                                                            address=Z1G_ADDRESS;
                                                            break;
                                                    case Z1G_ADDRESS:
                                                            aBuffer[6] |= m_CAL_RSP_BYTE6_z1g(word);
                                                            aBuffer[7] =  m_CAL_RSP_BYTE7_z1g(word);
                                                            aBuffer[8] =  m_CAL_RSP_BYTE8_z1g(word);
                                                            address=Z1NG_ADDRESS;
                                                            break;
                                                    case Z1NG_ADDRESS:
                                                            aBuffer[8] |= m_CAL_RSP_BYTE8_zn1g(word);
                                                            aBuffer[9] = m_CAL_RSP_BYTE9_zn1g(word);
                                                            processed_counter=command_counter;
                                                            response_length=10;
                                                            break;
                                                    default:
                                                            aBuffer[0]= m_CAL_RSP_BYTE0; 
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
