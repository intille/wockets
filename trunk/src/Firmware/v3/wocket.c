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
uint8_t EEMEM _NV_TM;
uint8_t EEMEM _NV_SENS;

#define _DEFAULTBTCAL100 725
#define _DEFAULTBTCAL80 680
#define _DEFAULTBTCAL60 640
#define _DEFAULTBTCAL40 600
#define _DEFAULTBTCAL20 560
#define _DEFAULTBTCAL10 540

uint16_t EEMEM _NV_BTCAL100;
uint16_t EEMEM _NV_BTCAL80;
uint16_t EEMEM _NV_BTCAL60;
uint16_t EEMEM _NV_BTCAL40;
uint16_t EEMEM _NV_BTCAL20;
uint16_t EEMEM _NV_BTCAL10;

unsigned int _wBTCAL100;
unsigned int _wBTCAL80;
unsigned int _wBTCAL60;
unsigned int _wBTCAL40;
unsigned int _wBTCAL20;
unsigned int _wBTCAL10;

#define _DEFAULT_X1G_CAL 500
#define _DEFAULT_XN1G_CAL 501
#define _DEFAULT_Y1G_CAL 502
#define _DEFAULT_YN1G_CAL 503
#define _DEFAULT_Z1G_CAL 504
#define _DEFAULT_ZN1G_CAL 505

uint16_t EEMEM _NV_X1G_CAL;
uint16_t EEMEM _NV_XN1G_CAL;
uint16_t EEMEM _NV_Y1G_CAL;
uint16_t EEMEM _NV_YN1G_CAL;
uint16_t EEMEM _NV_Z1G_CAL;
uint16_t EEMEM _NV_ZN1G_CAL;

unsigned int _wX1G_CAL;
unsigned int _wXN1G_CAL;
unsigned int _wY1G_CAL;
unsigned int _wYN1G_CAL;
unsigned int _wZ1G_CAL;
unsigned int _wZN1G_CAL;


unsigned char _INITIALIZED=0;
unsigned char _STATUS_BYTE=0;
unsigned char _SAMPLING_RATE=90;
unsigned char _wTCNT2_reps=1;
unsigned char _wTCNT2=0;
unsigned char _wTCNT2_last=0;
unsigned char _wTM=_TM_Continuous;
unsigned char _wSENS=_4_G;

unsigned long _wPC=0;

uint8_t EEMEM _NV_PDT;
#define _DEFAULT_PDT 127
unsigned char _wPDT;
uint32_t _wShutdownTimer=0;
uint32_t _DEFAULT_SHUTDOWN=0;



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


	/* Blink yellow for 5 seconds if battery not fully charged */
	unsigned short battery=_atmega_a2dConvert10bit(IN_VSENSE_BAT);
	if (battery<700)
	{
		for (int i=0;(i<3);i++){
			_yellowled_turn_on();		
			for(int j=0;(j<200);j++)
				_delay_ms(5);
			_yellowled_turn_off();
			for(int j=0;(j<200);j++)
				_delay_ms(5);
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
	


	//eeprom_write_byte(&_NV_DEBUG,_INITIALIZED);	
	/* If the wocket has been initialized */
	if (_INITIALIZED==_WOCKET_INITIALIZED)
	{
		// Read the sampling rate from the EEPROM
		if (battery>300)
		{
			_SAMPLING_RATE=eeprom_read_byte(&_NV_SAMPLING_RATE);
			_STATUS_BYTE=eeprom_read_byte(&_NV_STATUS_BYTE);
			_wTM=eeprom_read_byte(&_NV_TM);
			_wSENS=eeprom_read_byte(&_NV_SENS);

			_wBTCAL100=eeprom_read_word(&_NV_BTCAL100);
			_wBTCAL80=eeprom_read_word(&_NV_BTCAL80);
			_wBTCAL60=eeprom_read_word(&_NV_BTCAL60);
			_wBTCAL40=eeprom_read_word(&_NV_BTCAL40);
			_wBTCAL20=eeprom_read_word(&_NV_BTCAL20);
			_wBTCAL10=eeprom_read_word(&_NV_BTCAL10);


			_wX1G_CAL=eeprom_read_word(&_NV_X1G_CAL);
			_wXN1G_CAL=eeprom_read_word(&_NV_XN1G_CAL);
			_wY1G_CAL=eeprom_read_word(&_NV_Y1G_CAL);
			_wYN1G_CAL=eeprom_read_word(&_NV_YN1G_CAL);
			_wZ1G_CAL=eeprom_read_word(&_NV_Z1G_CAL);
			_wZN1G_CAL=eeprom_read_word(&_NV_ZN1G_CAL);

			_wPDT=eeprom_read_byte(&_NV_PDT);

		}

		// Load the transmission mode						
		_greenled_turn_on();		
		for(int i=0;(i<200);i++)
			_delay_ms(5);
		_greenled_turn_off();		
	}
	/* If the wocket has never been initialized, write the default settings and blink green for 5 seconds */
	else
	{

		// Set the sampling rate to 90Hz
		//_SAMPLING_RATE=40;
		//_wTM=_TM_Burst_60;

		_SAMPLING_RATE=90;
		_wTM=_TM_Continuous;
	
		// Write the sampling rate to the EEPROM
		if (battery>300)
		{
			eeprom_write_byte(&_NV_SAMPLING_RATE,_SAMPLING_RATE);
			eeprom_write_byte(&_NV_TM,_wTM);
			eeprom_write_byte(&_NV_STATUS_BYTE,0x00);
			eeprom_write_byte(&_NV_SENS,_wSENS);

			//Set default battery calibration values
			eeprom_write_word(&_NV_BTCAL100,_DEFAULTBTCAL100);
			eeprom_write_word(&_NV_BTCAL80,_DEFAULTBTCAL80);
			eeprom_write_word(&_NV_BTCAL60,_DEFAULTBTCAL60);
			eeprom_write_word(&_NV_BTCAL40,_DEFAULTBTCAL40);
			eeprom_write_word(&_NV_BTCAL20,_DEFAULTBTCAL20);
			eeprom_write_word(&_NV_BTCAL10,_DEFAULTBTCAL10);

			_wBTCAL100=_DEFAULTBTCAL100;
			_wBTCAL80=_DEFAULTBTCAL80;
			_wBTCAL60=_DEFAULTBTCAL60;
			_wBTCAL40=_DEFAULTBTCAL40;
			_wBTCAL20=_DEFAULTBTCAL20;
			_wBTCAL10=_DEFAULTBTCAL10;

			//Set default acc calibration values
			eeprom_write_word(&_NV_X1G_CAL,_DEFAULT_X1G_CAL);
			eeprom_write_word(&_NV_XN1G_CAL,_DEFAULT_XN1G_CAL);
			eeprom_write_word(&_NV_Y1G_CAL,_DEFAULT_Y1G_CAL);
			eeprom_write_word(&_NV_YN1G_CAL,_DEFAULT_YN1G_CAL);
			eeprom_write_word(&_NV_Z1G_CAL,_DEFAULT_Z1G_CAL);
			eeprom_write_word(&_NV_ZN1G_CAL,_DEFAULT_ZN1G_CAL);

			_wX1G_CAL=_DEFAULT_X1G_CAL;
			_wXN1G_CAL=_DEFAULT_XN1G_CAL;
			_wY1G_CAL=_DEFAULT_Y1G_CAL;
			_wYN1G_CAL=_DEFAULT_YN1G_CAL;
			_wZ1G_CAL=_DEFAULT_Z1G_CAL;
			_wZN1G_CAL=_DEFAULT_ZN1G_CAL;

			//SET the PDT
			_wPDT=_DEFAULT_PDT;
			eeprom_write_byte(&_NV_PDT,_wPDT);

		}

		// Set the initialized flag in the status byte
		_INITIALIZED=_WOCKET_INITIALIZED;

		// Write the status byte to the EEPROM		
		eeprom_write_byte(&_NV_INITIALIZED,_INITIALIZED);
				
		// Blink green for 5 seconds	
		for (int i=0;(i<3);i++){
			_greenled_turn_on();		
			for(int j=0;(j<200);j++)
				_delay_ms(5);
			_greenled_turn_off();
			for(int j=0;(j<200);j++)
				_delay_ms(5);
		}		
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

	_DEFAULT_SHUTDOWN= (unsigned long)_wPDT*(unsigned long)_SAMPLING_RATE* (unsigned long)60;
	_wShutdownTimer=_DEFAULT_SHUTDOWN;



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



/*
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
*/
void _send_uncompressed_pdu(unsigned short x, unsigned short y, unsigned short z)
{
	aBuffer[0] =0x80| ((x>>8)& 0x03);
	_bluetooth_transmit_uart0_byte(aBuffer[0]);
	aBuffer[1] = ((unsigned char) ((x>>1)&0x7f));
	_bluetooth_transmit_uart0_byte(aBuffer[1]);
	aBuffer[2] = ((unsigned char) ((x<<6) &0x40)) | ((unsigned char) ((y>>4)&0x3f));
	_bluetooth_transmit_uart0_byte(aBuffer[2]);
	aBuffer[3] = ((unsigned char) ((y<<3) &0x78)) | ((unsigned char) ((z>>7)&0x07));
	_bluetooth_transmit_uart0_byte(aBuffer[3]);
	aBuffer[4] = ((unsigned char) (z&0x7f));
	_bluetooth_transmit_uart0_byte(aBuffer[4]);
}


void _send_compressed_pdu(unsigned char x, unsigned char y, unsigned char z)
{
	aBuffer[0] =0xe0| ((x>>1)& 0x1f);
	_bluetooth_transmit_uart0_byte(aBuffer[0]);
	aBuffer[1] = ((x & 0x01)<<6) | (y & 0x3f);
	_bluetooth_transmit_uart0_byte(aBuffer[1]);
	aBuffer[2] =  (z<<1);
	_bluetooth_transmit_uart0_byte(aBuffer[2]);	
}

void _send_batch_count(unsigned short count)
{
 
    aBuffer[0]=m_BC_RSP_BYTE0;
    aBuffer[1]=m_BC_RSP_BYTE1(count);
    aBuffer[2]=m_BC_RSP_BYTE2(count);
	for (int i=0;(i<3);i++)                                                                                       
       	_bluetooth_transmit_uart0_byte(aBuffer[i]); 
 
}

void _send_summary_count(unsigned short count)
{
 
    aBuffer[0]=m_AC_RSP_BYTE0;
    aBuffer[1]=m_AC_RSP_BYTE1(count);
    aBuffer[2]=m_AC_RSP_BYTE2(count);
	aBuffer[3]=m_AC_RSP_BYTE3(count);
	for (int i=0;(i<4);i++)                                                                                       
       	_bluetooth_transmit_uart0_byte(aBuffer[i]); 
 
}

void _send_sr()
{
 
	aBuffer[0]=m_SR_RSP_BYTE0;
    aBuffer[1]=m_SR_RSP_BYTE1(_SAMPLING_RATE);
	for (int i=0;(i<2);i++)                                                                                       
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
			//	_transmit_packet(_encode_packet(xs[mycounter],ys[mycounter],zs[mycounter]));
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
#ifdef _VERSION==3
		x=_atmega_a2dConvert10bit(ADC2);
		y=_atmega_a2dConvert10bit(ADC1);
		z=_atmega_a2dConvert10bit(ADC0);

#else
		x=_atmega_a2dConvert10bit(ADC3);
		y=_atmega_a2dConvert10bit(ADC2);
		z=_atmega_a2dConvert10bit(ADC1);
		_transmit_packet(_encode_packet(x,y,z));	
#endif


		
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
				case (unsigned char)GET_BTCAL:
				case (unsigned char) GET_HV:
				case (unsigned char) GET_FV:				
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
				case (unsigned char) SET_BTCAL:
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
#ifdef _VERSION==3
                            word=_atmega_a2dConvert10bit(ADC7);
#else
                            word=_atmega_a2dConvert10bit(ADC4);
#endif				  

                            aBuffer[0]=m_BL_RSP_BYTE0;
                            aBuffer[1]=m_BL_RSP_BYTE1(word);
                            aBuffer[2]=m_BL_RSP_BYTE2(word);
                            processed_counter=command_counter;
                            response_length=3;		                                                                          
                            break;		
                case (unsigned char) GET_SEN:           			  
                            aBuffer[0]=m_SENS_RSP_BYTE0;
                            aBuffer[1]=m_SENS_RSP_BYTE1(_wSENS);                       
                            processed_counter=command_counter;
                            response_length=2;		                                                                          
                            break;	
                case (unsigned char) GET_BP:           
#ifdef _VERSION==3
                            word=_atmega_a2dConvert10bit(ADC7);
#else
                            word=_atmega_a2dConvert10bit(ADC4);
						
#endif				  
							if (word>_wBTCAL100)
								word=100;
							else if (word>_wBTCAL80)
								word=80 + ((word- _wBTCAL80)*20) / (_wBTCAL100-_wBTCAL80);
							else if (word>_wBTCAL60)
								word=60 + ((word- _wBTCAL60)*20) / (_wBTCAL80-_wBTCAL60);
							else if (word>_wBTCAL40)
								word=40 + ((word- _wBTCAL40)*20) / (_wBTCAL60-_wBTCAL40);
							else if (word>_wBTCAL20)
								word=20 + ((word- _wBTCAL20)*20) / (_wBTCAL40-_wBTCAL20);
							else if (word>_wBTCAL10)
								word=10 + ((word- _wBTCAL10)*10) / (_wBTCAL20-_wBTCAL10);
							else
								word=0;

                            aBuffer[0]=m_BP_RSP_BYTE0;
                            aBuffer[1]=m_BP_RSP_BYTE1(word);      ;
                            processed_counter=command_counter;
                            response_length=2;		                                                                          
                            break;
 				   case (unsigned char) GET_PDT:  
				   		aBuffer[0]=m_PDT_RSP_BYTE0;
                        aBuffer[1]=m_PDT_RSP_BYTE1(_wPDT);
						processed_counter=command_counter;
						response_length=2;
						break;			
                   case (unsigned char) SET_PDT:  
				   		_wPDT=m_SET_PDT(aBuffer[1]);
						eeprom_write_byte(&_NV_PDT,_wPDT);
						processed_counter=command_counter;
						break;																				
                   case (unsigned char) GET_SR:  
				   		aBuffer[0]=m_SR_RSP_BYTE0;
                        aBuffer[1]=m_SR_RSP_BYTE1(_SAMPLING_RATE);
						processed_counter=command_counter;
						response_length=2;
						break;
                case (unsigned char) GET_PC:  
				   		aBuffer[0]=m_PC_RSP_BYTE0;
                        aBuffer[1]=m_PC_RSP_BYTE1(_wPC);
						aBuffer[2]=m_PC_RSP_BYTE2(_wPC);
                        aBuffer[3]=m_PC_RSP_BYTE3(_wPC);
						aBuffer[4]=m_PC_RSP_BYTE4(_wPC);
                        aBuffer[5]=m_PC_RSP_BYTE5(_wPC);
						processed_counter=command_counter;
						response_length=6;
						break;
                   case (unsigned char) SET_SR:  
				   		_SAMPLING_RATE=m_SET_SR(aBuffer[1]);
						_wocket_initialize_timer2_interrupt();
						eeprom_write_byte(&_NV_SAMPLING_RATE,_SAMPLING_RATE);
						processed_counter=command_counter;
						break;

     			 case (unsigned char) GET_TM:  
				   		aBuffer[0]=m_TM_RSP_BYTE0;
                        aBuffer[1]=m_TM_RSP_BYTE1(_wTM);
						processed_counter=command_counter;
						response_length=2;
						break;
                   case (unsigned char) SET_TM:  
				   		_wTM=m_SET_TM(aBuffer[1]);
						eeprom_write_byte(&_NV_TM,_wTM);
						processed_counter=command_counter;
						break;
                    case (unsigned char) SET_CAL:                                                                    
                            if (eeprom_is_ready())
                            {
                                    //do nothing if battery is low
#ifdef _VERSION==3
                                    if (_atmega_a2dConvert10bit(ADC7)<600)
#else
                                    if (_atmega_a2dConvert10bit(ADC4)<600)
#endif
                                            break;
                                    else
                                    {   
										_wX1G_CAL=m_SET_CAL_x1g(aBuffer[1],aBuffer[2]);
										eeprom_write_word(&_NV_X1G_CAL,_wX1G_CAL);
										_wXN1G_CAL=m_SET_CAL_xn1g(aBuffer[2],aBuffer[3]);
										eeprom_write_word(&_NV_XN1G_CAL,_wXN1G_CAL);
										_wY1G_CAL=m_SET_CAL_y1g(aBuffer[3],aBuffer[4],aBuffer[5]);
										eeprom_write_word(&_NV_Y1G_CAL,_wY1G_CAL);
										_wYN1G_CAL= m_SET_CAL_yn1g(aBuffer[5],aBuffer[6]);
										eeprom_write_word(&_NV_YN1G_CAL,_wYN1G_CAL);
										_wZ1G_CAL= m_SET_CAL_z1g(aBuffer[6],aBuffer[7],aBuffer[8]);
										eeprom_write_word(&_NV_Z1G_CAL,_wZ1G_CAL);
										_wZN1G_CAL=m_SET_CAL_zn1g(aBuffer[8],aBuffer[8]);
										eeprom_write_word(&_NV_ZN1G_CAL,_wZN1G_CAL);
										processed_counter=command_counter;

                                    }                                                                                                                                                                                                                                                       
                                                                                                                                    
                            }                                                                                                                       
                            //enable global interrupts
                            break;
                    case (unsigned char) GET_CAL:    
							                                                              
							aBuffer[0]= m_CAL_RSP_BYTE0;
                            aBuffer[1]= m_CAL_RSP_BYTE1_x1g(_wX1G_CAL);                                                                   
                            aBuffer[2]= m_CAL_RSP_BYTE2_x1g(_wX1G_CAL);
							aBuffer[2]|= m_CAL_RSP_BYTE2_xn1g(_wXN1G_CAL);
                            aBuffer[3] = m_CAL_RSP_BYTE3_xn1g(_wXN1G_CAL);
							aBuffer[3]|= m_CAL_RSP_BYTE3_y1g(_wY1G_CAL);
                            aBuffer[4] = m_CAL_RSP_BYTE4_y1g(_wY1G_CAL);
                            aBuffer[5] = m_CAL_RSP_BYTE5_y1g(_wY1G_CAL);
                            aBuffer[5]|= m_CAL_RSP_BYTE5_yn1g(_wYN1G_CAL);
                            aBuffer[6] = m_CAL_RSP_BYTE6_yn1g(_wYN1G_CAL);
							aBuffer[6] |= m_CAL_RSP_BYTE6_z1g(_wZ1G_CAL);
                            aBuffer[7] =  m_CAL_RSP_BYTE7_z1g(_wZ1G_CAL);
                            aBuffer[8] =  m_CAL_RSP_BYTE8_z1g(_wZ1G_CAL);
							aBuffer[8] |= m_CAL_RSP_BYTE8_zn1g(_wZN1G_CAL);
                            aBuffer[9] =  m_CAL_RSP_BYTE9_zn1g(_wZN1G_CAL);
							processed_counter=command_counter;
                            response_length=10;                                                                               
                            break;    
                    case (unsigned char) GET_BTCAL:    
							                                                              
							aBuffer[0]= m_BTCAL_RSP_BYTE0;
                            aBuffer[1]= m_BTCAL_RSP_BYTE1_100(_wBTCAL100);                                                                   
                            aBuffer[2]= m_BTCAL_RSP_BYTE2_100(_wBTCAL100);
							aBuffer[2]|= m_BTCAL_RSP_BYTE2_80(_wBTCAL80);
                            aBuffer[3] = m_BTCAL_RSP_BYTE3_80(_wBTCAL80);
							aBuffer[3]|= m_BTCAL_RSP_BYTE3_60(_wBTCAL60);
                            aBuffer[4] = m_BTCAL_RSP_BYTE4_60(_wBTCAL60);
                            aBuffer[5] = m_BTCAL_RSP_BYTE5_60(_wBTCAL60);
                            aBuffer[5]|= m_BTCAL_RSP_BYTE5_40(_wBTCAL40);
                            aBuffer[6] = m_BTCAL_RSP_BYTE6_40(_wBTCAL40);
							aBuffer[6] |= m_BTCAL_RSP_BYTE6_20(_wBTCAL20);
                            aBuffer[7] =  m_BTCAL_RSP_BYTE7_20(_wBTCAL20);
                            aBuffer[8] =  m_BTCAL_RSP_BYTE8_20(_wBTCAL20);
							aBuffer[8] |= m_BTCAL_RSP_BYTE8_10(_wBTCAL10);
                            aBuffer[9] =  m_BTCAL_RSP_BYTE9_10(_wBTCAL10);
							processed_counter=command_counter;
                            response_length=10;                                                                               
                            break;  
 					case (unsigned char) SET_BTCAL:
                            if (eeprom_is_ready())
                            {
                                    //do nothing if battery is low
#ifdef _VERSION==3
                                    if (_atmega_a2dConvert10bit(ADC7)<600)
#else
                                    if (_atmega_a2dConvert10bit(ADC4)<600)
#endif
                                            break;
                                    else
                                    {   
										_wBTCAL100=m_SET_BTCAL_100(aBuffer[1],aBuffer[2]);
										eeprom_write_word(&_NV_BTCAL100,_wBTCAL100);
										_wBTCAL80=m_SET_BTCAL_80(aBuffer[2],aBuffer[3]);
										eeprom_write_word(&_NV_BTCAL80,_wBTCAL80);
										_wBTCAL60=m_SET_BTCAL_60(aBuffer[3],aBuffer[4],aBuffer[5]);
										eeprom_write_word(&_NV_BTCAL60,_wBTCAL60);
										_wBTCAL40= m_SET_BTCAL_40(aBuffer[5],aBuffer[6]);
										eeprom_write_word(&_NV_BTCAL40,_wBTCAL40);
										_wBTCAL20= m_SET_BTCAL_20(aBuffer[6],aBuffer[7],aBuffer[8]);
										eeprom_write_word(&_NV_BTCAL20,_wBTCAL20);
										_wBTCAL10=m_SET_BTCAL_10(aBuffer[8],aBuffer[8]);
										eeprom_write_word(&_NV_BTCAL10,_wBTCAL10);
										processed_counter=command_counter;

                                    }                                                                                                                                                                                                                                                       
                                                                                                                                    
                            }                                                                                                                       
                            //enable global interrupts
                            break;	
	   				case (unsigned char) GET_HV:  
				   		aBuffer[0]=m_HV_RSP_BYTE0;
                        aBuffer[1]=m_HV_RSP_BYTE1(_VERSION);
						processed_counter=command_counter;		
						response_length=2;
						break;				
					case (unsigned char) GET_FV:  
				   		aBuffer[0]=m_FV_RSP_BYTE0;
                        aBuffer[1]=m_FV_RSP_BYTE1(_FVERSION);
						processed_counter=command_counter;
						response_length=2;
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
