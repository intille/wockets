//*****************************************************************************
//
// File Name    : 'mcu_atmega324p.c'
// Title        : ATmega324p microcontroller functions
// Author       : Fahd Albinali and Ranbel Sun
// Created      : 12/10/2008
// 
//  Description : These are functions that are specific to the atmega164p/atmega324p/atmega644p 
//  microcontroller
//                  
//
// This code is distributed under the MIT License
//     
//
//*****************************************************************************

#include "avr_general.h"
#include "mcu_atmega324p.h"
#include "acc_mma7260qt.h"
#include "bt_rn41.h"
#include <avr/io.h>
#include <avr/sfr_defs.h>
#include <avr/interrupt.h>
#include <avr/sleep.h>
#include <avr/wdt.h>
#include <util/delay.h>
#include <stdlib.h>
#include <avr/eeprom.h> 


void _atmega_set_adc_clock(unsigned char prescalar){
        if (prescalar==ADC_PRESCALAR_2){
                ADCSRA &= ~((1 << ADPS2) | (1 << ADPS1) | (1 << ADPS0));
        }else if (prescalar==ADC_PRESCALAR_4){
                ADCSRA &= ~((1 << ADPS2) | (1 << ADPS0));
                ADCSRA |= (1 << ADPS1);
        }else if (prescalar==ADC_PRESCALAR_8){
                ADCSRA &= ~(1 << ADPS2);
                ADCSRA |= ((1 << ADPS1) |(1 << ADPS0)) ;
        }else if (prescalar==ADC_PRESCALAR_16){
                ADCSRA &= ~((1 << ADPS1) |(1 << ADPS0));
                ADCSRA |= (1 << ADPS2);
        }else if (prescalar==ADC_PRESCALAR_32){
                ADCSRA &= ~(1 << ADPS1);
                ADCSRA |= ((1 << ADPS2)|(1 << ADPS0));
        }else if (prescalar==ADC_PRESCALAR_64){
                ADCSRA &= ~(1 << ADPS0);
                ADCSRA |= ((1 << ADPS2)|(1 << ADPS1));
        }else if (prescalar==ADC_PRESCALAR_128){            
                ADCSRA |= ((1 << ADPS2)|(1 << ADPS1)|(1 << ADPS0));
        }
}


void _atmega_adc_turn_on()
{

	sbi(ADCSRA,ADEN);
}


void _atmega_adc_turn_off()
{
	cbi(ADCSRA,ADEN);
}


void _atmega_select_adc(unsigned char channel){
        if (channel==ADC0){
                cbi(ADMUX,0);
                cbi(ADMUX,1);
                cbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }
        else if (channel==ADC1){
                sbi(ADMUX,0);
                cbi(ADMUX,1);
                cbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }else if (channel==ADC2){
                cbi(ADMUX,0);
                sbi(ADMUX,1);
                cbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }else if (channel==ADC3){
                sbi(ADMUX,0);
                sbi(ADMUX,1);
                cbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }else if (channel==ADC4){
                cbi(ADMUX,0);
                cbi(ADMUX,1);
                sbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }else if (channel==ADC6)
        {
                cbi(ADMUX,0);
                sbi(ADMUX,1);
                sbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }
        else if (channel==ADC7)
        {
                sbi(ADMUX,0);
                sbi(ADMUX,1);
                sbi(ADMUX,2);
                cbi(ADMUX,3);
                cbi(ADMUX,4);
        }
}


unsigned short _atmega_a2dConvert10bit(unsigned char channel){
	
	// Select channel
	_atmega_select_adc(channel);
	

	//Start ADC Conversion
	sbi(ADCSRA, ADIF);   // clear hardware "conversion complete" flag 
	sbi(ADCSRA,ADSC);
	
	// ADSC is 1 while converting, 0 when it is done
	while(bit_is_set(ADCSRA, ADSC)); 

	return ((ADCL)|((ADCH)<<8));
}

/* 
	Function Name: _atmega_initialize_uart0
	Parameters: None
	
	Description: This function enables UART0 to both transmit and receive data at an appropriate baud rate to the radio module
	
*/
void _atmega_initialize_uart0(unsigned int baud, unsigned char mode)
{
        /* Set baud rate */
        UBRR0H = (unsigned char)(baud>>8);
        UBRR0L = (unsigned char)baud;
        /* Enable receiver and/or transmitter */
		switch(mode)
		{
			case TX_UART_MODE:
        		UCSR0B = (1<<TXEN0);
				break;
			case RX_UART_MODE:
        		UCSR0B = (1<<RXEN0);
				break;
			default:
        		UCSR0B = (1<<TXEN0)|(1<<RXEN0);
		}
        /* Set frame format: 8data, 2stop bit */
        UCSR0C = (3<<UCSZ00);  //change 1 to 0 and &
}

/** 
	Function Name:_atmega_initialize_uart1
	Parameters: None
	
	Description: This function enables UART1 to both transmit and receive data at an appropriate baud rate to the radio module
	
*/
void _atmega_initialize_uart1(unsigned int baud, unsigned char mode)
{
        /* Set baud rate */
        UBRR1H = (unsigned char)(baud>>8);
        UBRR1L = (unsigned char)baud;
        /* Enable receiver and transmitter */
		switch(mode)
		{
			case TX_UART_MODE:
        		UCSR1B = (1<<TXEN1);
				break;
			case RX_UART_MODE:
        		UCSR1B = (1<<RXEN1);
				break;
			default:
        		UCSR1B = (1<<TXEN1)|(1<<RXEN1);
				break;
		}        
        /* Set frame format: 8data, 2stop bit */
        UCSR1C =(3<<UCSZ10);  //change 1 to 0 and &
}



/* 
	Function Name: _atmega_disable_JTAG
	Parameters: None
	
	Description: This function disables the JTAG interface by default.By default the interface is enabled.
	To disable it JTD has to be written logic 1 2 times in 4 cycles.
	
*/
void _atmega_disable_JTAG(void)
{
	unsigned char sreg;

	sreg = SREG;
	cli();
	MCUCR |= ( 1 <<JTD );
	MCUCR |= ( 1 <<JTD );
	SREG = sreg;
}


void _atmega_set_timer2_prescalar(unsigned char prescalar)
{
	switch(prescalar)
	{
		case CPU_CLK_PRESCALAR_NONE:
			TCCR2B |= (1 << CS20);
			break;
		case CPU_CLK_PRESCALAR_8:
			TCCR2B |= (1 << CS21); 
			break;
		case CPU_CLK_PRESCALAR_32:
			TCCR2B |= ((1 << CS20) | (1 << CS21));
			break;
		case CPU_CLK_PRESCALAR_64:
			TCCR2B |= (1 << CS22) ;
			break;
		case CPU_CLK_PRESCALAR_128:
			TCCR2B |= ((1 << CS20) |(1 << CS22));
			break;
		case CPU_CLK_PRESCALAR_256:
			TCCR2B |= ((1 << CS22) |(1 << CS21));
			break;
		default:
			TCCR2B |= ((1 << CS20) |(1 << CS21) | (1 << CS22)); 

	}
}

/* 
	Function Name: _atmega_enable_timer2
	Parameters: None
	
	Description: This function enables an 8-bit timer with a 1024 prescaler.and the overflow ISR TIMER2_OVF_vect
	
*/
void _atmega_enable_timer2(unsigned char timer_prescalar)
{

	// Setup the prescaler to 1024		 
	_atmega_set_timer2_prescalar(timer_prescalar);
	// Set the counter to 0
	TCNT2=0;
	//Enable the overflow interrupt
	TIMSK2 |= (1 << TOIE2); // Enable CTC interrupt
	// Enable global interrupts
	sei(); 
}


/* 
	Function Name: _atmega_disable_timer2
	Parameters: None
	
	Description: This function disables the timer 2 overflow interrupt
	
*/
void _atmega_disable_timer2(void)
{	
	//disable timer interrupt
	TIMSK2=0;
	// reset counter unit
	TCCR2B=0;
}



void _atmega_reset(void)
{               
        cli(); //irq's off
        wdt_enable(WDTO_15MS); //wd on,15ms
        while(1); //loop 
}


/* 
	Function Name: _atmega_disable_watchdog
	Parameters: None
	
	Description: This function prevents the watchdog timer configuration from being accidentally altered by a crashing application.
	This has to be done at the begining of an application
	
*/
void _atmega_disable_watchdog(void)
{
	MCUSR = 0;
	wdt_disable();
}

/* Exported Function Definitions */

/* 
	Function Name: _atmega_intialize
	Parameters: None
	
	Description: This function initializes the MCU. By default all pins are set as inputs to minize power consumption.
	
*/
void _atmega_initialize(unsigned char timer_prescalar)
{

	unsigned char prev_osccal=OSCCAL;
	unsigned char myosccal=0;

	//Turn on yellow LED while initializing		
	_yellowled_turn_on();
	

	//Set wocket status to off	
	wocket_status=0x00;

	//Disable watchdog timer
	//_atmega_disable_watchdog();

	// Disable JTAG interface
	_atmega_disable_JTAG();

	
	// By default initialize all ports as input to minimize power consumption
	// Setup Port A pins as input to minimize power consumption	
	cbi(DDRA,IN_VSENSE_COMP_PA0);
	cbi(DDRA,IN_ACCEL_Z_FILT_PA1);
	cbi(DDRA,IN_ACCEL_Y_FILT_PA2);
	cbi(DDRA,IN_ACCEL_X_FILT_PA3);
	cbi(DDRA,IN_VSENSE_BAT_PA4);
	cbi(DDRA,IN_USER_N_PA5);
	cbi(DDRA,FLOAT_PA6);
	cbi(DDRA,FLOAT_PA7);

	// Setup Port B pins as input to minimize power consumption
	cbi(DDRB,OUT_ACCEL_SEL1_PB0);	
	cbi(DDRB,OUT_ACCEL_SEL2_PB1);
	cbi(DDRB,IN_VSENSE_COMP_PB2);
	cbi(PORTB,IN_VSENSE_COMP_PB2);
	cbi(DDRB,OUT_ACCEL_SLEEP_N_PB3);
	cbi(DDRB,OUT_BT_SW_N_PB4);	
	cbi(DDRB,IN_CPU_PROG_MOSI_PB5);
	cbi(DDRB,OUT_CPU_PROG_MISO_PB6);	
	cbi(DDRB,IN_CPU_PROG_SCLK_PB7);	
	
	// Setup Port C pins as input to minimize power consumption
	cbi(DDRC,FLOAT_PC0);	
	cbi(DDRC,OUT_LED_GN_PC1);	
	//cbi(DDRC,OUT_LED_YE_PC2);	
	cbi(DDRC,FLOAT_PC3);	
	cbi(DDRC,FLOAT_PC4);	
	cbi(DDRC,FLOAT_PC5);	
	cbi(DDRC,FLOAT_PC6);	
	cbi(DDRC,FLOAT_PC7);	

	// Setup Port D pins as input to minimize power consumption
	cbi(DDRD,IN_BT_RXD_PD0);	
	cbi(DDRD,OUT_BT_TXD_PD1);	
	cbi(DDRD,OUT_BT_RESET_N_PD2);	
	cbi(DDRD,IN_VIB_SW_N_PD3);	
	cbi(DDRD,IN_BT_CONNECT_PD4);	
	cbi(DDRD,IN_BT_DISC_PD5);	
	cbi(DDRD,FLOAT_PD6);
	cbi(DDRD,FLOAT_PD7);	

	/* Set peripherials to the lowest power states */
	_bluetooth_turn_on();
	_accelerometer_turn_on();
	_accelerometer_set_sensitivity(_4G);

	/* Set UART */


	//First check if the radio is set at the correct baud rate
	//if the wocket yellow light does not go off, the wocket has not been
	
	_atmega_initialize_uart0(ATMEGA_BAUD_38400, TX_RX_UART_MODE);
	if ((_bluetooth_enter_command_mode()))
	{	
		_yellowled_turn_off();
		if (_bluetooth_get_baud_rate()==ATMEGA_BAUD_38400)
				_yellowled_turn_off();
	}else{

		
		// To run at 115K, we need to set the OSCCAL as follows, the value was
		// determined experimentally by trying different values	
		for (unsigned char i=0x50;(i<255);i++){
			OSCCAL= i;
			for (int j=0;(j<10);j++)
			{
				// To deal with a radio firmware bug, we are making sure the radio is set at the
				// correct baud rate of 38.4K
				_atmega_initialize_uart0(ATMEGA_BAUD_115200, TX_RX_UART_MODE);
				if ((_bluetooth_enter_command_mode()))
				{	
				//_yellowled_green_on();
					if (_bluetooth_set_baud_rate(ATMEGA_BAUD_38400))
					{
						_bluetooth_reset();	
						_atmega_initialize_uart0(ATMEGA_BAUD_38400, TX_RX_UART_MODE);						
						_yellowled_turn_off();
						//_atmega_reset();
						break;
					}
				}

			}
		}
		OSCCAL= prev_osccal;	
	}

	_atmega_initialize_uart0(ATMEGA_BAUD_38400, TX_RX_UART_MODE);
	/* Set ADC for conversion */    
    //Set ADC reference to AVCC
     ADMUX |=(1 << REFS0);
     //Set the ADC conversion clock prescalar       
     _atmega_set_adc_clock(ADC_PRESCALAR_64);
     _atmega_adc_turn_on();

     /* Enable Timer 2 */
     _atmega_enable_timer2(timer_prescalar);


}


/* 
	Function Name: _atmega_finalize
	Parameters: None
	
	Description: This function shuts down all peripherals and makes sure that the device is in its lowest power state
	
*/
void _atmega_finalize(void)
{
	cli();
	_bluetooth_turn_off();
	_accelerometer_turn_off();
	_greenled_turn_off();
	_yellowled_turn_off();

	//Set all ports as inputs
	DDRA=0x00;
	DDRB=0x00;
	DDRC=0x00;
	DDRD=0x00;

	PORTA=0x00;
	PORTB=0x00;
	PORTC=0x00;
	PORTD=0x00;

	// Disable timer
	_atmega_disable_timer2();

	//Disable watchdog
	wdt_disable();

	//Disable ADC Conversion
	_atmega_adc_turn_off();


	// Disable pull-ups
  	MCUCR |= (1u << PUD); 
	// Disable Analog comparitor
  	ACSR &= ~(1<<ACIE);   // Disable analog comparator interrupt
  	ACSR |= (1<<ACD);     // Disable analog comparitor 
	// Power Reduction Register, everything off;
  	PRR |= (uint8_t)((1<<PRADC)|(1<<PRSPI)|(1<<PRTIM0)|(1<<PRTIM1)|(1<<PRTWI)); 

	//Power down the MCU

	sleep_enable();
    sleep_bod_disable();
    sei();	
	set_sleep_mode(SLEEP_MODE_PWR_DOWN);
	sleep_cpu();
    sleep_disable();

}




/* Bluetooth Functions */

unsigned char _bluetooth_enter_command_mode(void)
{
	unsigned char attempts=0;
	unsigned char aByte=0;
	unsigned char count=0;

	while(1)  
	{   
		//for (int i=0;(i<255);i++)        
		_bluetooth_transmit_uart0_byte('$');	
		_delay_ms(5);	
		_bluetooth_transmit_uart0_byte('$');		
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte('$');		
		_delay_ms(5);
		//_bluetooth_transmit_uart0_byte('$');		
		
		//for (int i=0;(i<10);i++)        		
		
		
		_bluetooth_transmit_uart0_byte(13);
		_bluetooth_transmit_uart0_byte(13);
		/*_bluetooth_transmit_uart0_byte(13);
		_bluetooth_transmit_uart0_byte(13);
		_bluetooth_transmit_uart0_byte(13);*/

		attempts++;

		if (_bluetooth_receive_uart0_byte(&aByte))
		{		
				if (aByte=='C'){					
					_bluetooth_transmit_uart0_byte(13);						
					for (int i=0;(i<10);i++)        		
						_bluetooth_transmit_uart0_byte(13);
					return 1;	
				}
		}

 		if (attempts>=255) 
			break;				
	}

	
	return 0;
}


unsigned char _bluetooth_exit_command_mode(void)
{
	unsigned char attempts=0;
	unsigned char aByte=0;

	while(1)  
	{           
		_bluetooth_transmit_uart0_byte('-');		
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte('-');		
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte('-');		
		_delay_ms(5);
				
		_bluetooth_transmit_uart0_byte(13);
		_bluetooth_transmit_uart0_byte(13);
		attempts++;

 		if ((attempts>=255) || (_bluetooth_receive_uart0_byte(&aByte)==0))
			break;				
	}

	// succeeded in entering command mode
	if (attempts<255)
		return 1;
	
	return 0;
}


void _bluetooth_reset(void)
{
	_bluetooth_turn_off();
	_delay_ms(5);
	_bluetooth_turn_on();

}

unsigned char _bluetooth_set_baud_rate(unsigned char baudrate)
{
	unsigned char attempts=0;
	unsigned char aByte=0;

	while(1)  
	{   
		for (int i=0;(i<100);i++)
			_bluetooth_receive_uart0_byte(&aByte);

		_bluetooth_transmit_uart0_byte(13);
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte(13);

		_bluetooth_transmit_uart0_byte('S');
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte('U');
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte(',');
		_delay_ms(5);
		switch(baudrate){
			case ATMEGA_BAUD_2400:
				_bluetooth_transmit_uart0_byte('2');
				_bluetooth_transmit_uart0_byte('4');
				break;
			case ATMEGA_BAUD_4800:
				_bluetooth_transmit_uart0_byte('4');
				_bluetooth_transmit_uart0_byte('8');
				break;
			case ATMEGA_BAUD_9600:
				_bluetooth_transmit_uart0_byte('9');
				_bluetooth_transmit_uart0_byte('6');
				break;
			case ATMEGA_BAUD_19200:
				_bluetooth_transmit_uart0_byte('1');
				_bluetooth_transmit_uart0_byte('9');
				break;
			case ATMEGA_BAUD_28800:
				_bluetooth_transmit_uart0_byte('2');
				_bluetooth_transmit_uart0_byte('8');
				break;
			case ATMEGA_BAUD_38400:
				_bluetooth_transmit_uart0_byte('3');
				_delay_ms(5);
				_bluetooth_transmit_uart0_byte('8');
				_delay_ms(5);
				break;
			case ATMEGA_BAUD_57600:
				_bluetooth_transmit_uart0_byte('5');
				_bluetooth_transmit_uart0_byte('7');
				break;
			case ATMEGA_BAUD_115200:
				_bluetooth_transmit_uart0_byte('1');
				_bluetooth_transmit_uart0_byte('1');
				break;
			case ATMEGA_BAUD_230000:
				_bluetooth_transmit_uart0_byte('2');
				_bluetooth_transmit_uart0_byte('3');
				break;
			case ATMEGA_BAUD_460000:
				_bluetooth_transmit_uart0_byte('4');
				_bluetooth_transmit_uart0_byte('6');
				break;
			default:
			_bluetooth_transmit_uart0_byte('3');
			_bluetooth_transmit_uart0_byte('8');
		}

		_bluetooth_transmit_uart0_byte(13);
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte(13);
		_delay_ms(5);

		attempts++;
		if (_bluetooth_receive_uart0_byte(&aByte))
		{
			if (aByte=='A')			
				return 1;					
		}
		if (attempts>=255)
			break;
	}
	
	// succeeded in entering command mode

	return 0;
}


unsigned char _bluetooth_get_baud_rate()
{
	unsigned char attempts=0;
	unsigned char baudrate=0;
	unsigned char aByte=0;

	while(1)  
	{            


		//for (int i=0;(i<100);i++)
		//	_bluetooth_receive_uart0_byte(&aByte);

		_bluetooth_transmit_uart0_byte(13);
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte(13);


		_bluetooth_transmit_uart0_byte('G');
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte('U');		
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte(13);
		_delay_ms(5);
		_bluetooth_transmit_uart0_byte(13);
		_delay_ms(5);


		attempts++;
 		if ((attempts>=255) || (_bluetooth_receive_uart0_byte(&baudrate)==0))
			break;

	}
	if (attempts<255)
	{	
		switch(baudrate)
		{
			case '2':
				baudrate=ATMEGA_BAUD_2400;
				break;
			case '4':
				baudrate=ATMEGA_BAUD_4800;
				break;
			case '9':
				baudrate=ATMEGA_BAUD_9600;
				break;
			case '1':
				baudrate=ATMEGA_BAUD_115200;
				break;
			case '5':
				baudrate=ATMEGA_BAUD_57600;
				break;
			default:
				baudrate=ATMEGA_BAUD_38400;
				break;
			}
	}
	
	return baudrate;
}

/*unsigned char _bluetooth_initialize(unsigned baudrate)
{
	if (_bluetooth_enter_command_mode()){
		_greenled_turn_on();
		if (_bluetooth_set_baud_rate(baudrate))
		{
			_bluetooth_reset();	
			return 1;
		}
	}

	return 0;

}*/
/* 
	Function Name: _rn41_on
	Parameters: None
	
	Description: This function turns on the bluetooth RN-41 module and sets the pins properly
	
*/
void _bluetooth_turn_on(void)
{
	// Set the direction of TX pin as output
	sbi(DDRD,OUT_BT_TXD_PD1);

	// Set the direction of the RESET pin as output and high
	sbi(DDRD,OUT_BT_RESET_N_PD2);	
	sbi(PORTD,OUT_BT_RESET_N_PD2);  

	// Set the direction of the switch pin as output and low
	sbi(DDRB,OUT_BT_SW_N_PB4);
	cbi(PORTB,OUT_BT_SW_N_PB4);

	// Set the status of the bluetooth to true
	sbi(wocket_status, BIT0_BLUETOOTH_STATUS);
}

/* 
	Function Name: _rn41_off
	Parameters: None
	
	Description: This function turns off the bluetooth RN-41 module and sets the pins as inputs to reduce power consumption
	
*/
void _bluetooth_turn_off(void)
{
	// Set the direction of TX, RESET and switch pins as input
	cbi(DDRD,OUT_BT_TXD_PD1);
	cbi(DDRD,OUT_BT_RESET_N_PD2);
	cbi(DDRB,OUT_BT_SW_N_PB4);		 

	// Set the status of bluetooth to false
	cbi(wocket_status, BIT0_BLUETOOTH_STATUS);
}


/* 
	Function Name: _is_bluetooth_on
	Parameters: None
	
	Description: Tests if the bluetooth status bit is on
	
*/

unsigned char _is_bluetooth_on(void)
{
	return ((wocket_status>>BIT0_BLUETOOTH_STATUS) & 0x01);
}



unsigned char _bluetooth_is_connected(void){

        return (0x01 & (PIND>>IN_BT_CONNECT_PD4));


}


unsigned char _bluetooth_is_discoverable(void){

        return (0x01 & (PIND>>IN_BT_DISC_PD5));
}


unsigned char _bluetooth_receive_uart0_byte(unsigned char *data)
  {
  	int count=0;
   while ( !(UCSR0A &  (1<<RXC0)) )
   {
   		if (count++==1) return 0; //timed out
   		//	_delay_ms(1);
   }     /*  Wait for incoming data   */

   *data=UDR0;

   return 1;/* Return success*/
  }


void _bluetooth_transmit_uart0_byte( unsigned char data )
{
  while ( !(UCSR0A & (1<<UDRE0)) );        /* Wait for   empty transmit buffer */
  UCSR0A=UCSR0A & 0xdf;
  
  UDR0 =  data;  /* Start transmission   */
   
}



/* Accelerometer Functions */

unsigned char _accelerometer_set_sensitivity(unsigned char level){
  	
	if (level==_1_5G){
		cbi(PORTB,OUT_ACCEL_SEL1_PB0);
		cbi(PORTB,OUT_ACCEL_SEL2_PB1);
		return _1_5G;
	}else if (level==_2G){
		sbi(PORTB,OUT_ACCEL_SEL1_PB0);
		cbi(PORTB,OUT_ACCEL_SEL2_PB1);
		return _2G;
	}else if (level==_4G){
		sbi(PORTB,OUT_ACCEL_SEL1_PB0);
		cbi(PORTB,OUT_ACCEL_SEL2_PB1);
		return _4G;
	}else if (level==_6G){
		sbi(PORTB,OUT_ACCEL_SEL1_PB0);
		sbi(PORTB,OUT_ACCEL_SEL2_PB1);
		return _6G;
	}

	return 0;
}


/* 
	Function Name: _accelerometer_turn_on
	Parameters: None
	
	Description: This function turns on the accelerometer module and sets the pins properly
	
*/
void _accelerometer_turn_on(void)
{
	sbi(DDRB,OUT_ACCEL_SEL1_PB0);	
	sbi(DDRB,OUT_ACCEL_SEL2_PB1);
	sbi(DDRB,OUT_ACCEL_SLEEP_N_PB3);
	sbi(PORTB,OUT_ACCEL_SLEEP_N_PB3);	 
	 			
	// Set the status of the accelerometer to true
	sbi(wocket_status, BIT1_ACCELEROMETER_STATUS);
}

/* 
	Function Name: _accelerometer_turn_off
	Parameters: None
	
	Description: This function turns off the accelerometer module and sets the pins as inputs to reduce power consumption
	
*/
void _accelerometer_turn_off(void)
{
	 _accelerometer_set_sensitivity(_1_5G);
	 cbi(DDRB,OUT_ACCEL_SEL1_PB0);	
	 cbi(DDRB,OUT_ACCEL_SEL2_PB1);
	 sbi(DDRB,OUT_ACCEL_SLEEP_N_PB3); //sleep pin in output mode
	 cbi(PORTB,OUT_ACCEL_SLEEP_N_PB3); //clear the pin	 
	 
	 // Set the status of the accelerometer to false
	 cbi(wocket_status, BIT1_ACCELEROMETER_STATUS);
}

/* 
	Function Name: _is_accelerometer_on
	Parameters: None
	
	Description: Tests if the accelerometer status bit is on
	
*/

unsigned char _is_accelerometer_on(void)
{
	return ((wocket_status>>BIT1_ACCELEROMETER_STATUS) & 0x01);
}
/* LED Control Functions */


/* 
	Function Name: _greenled_turn_on
	Parameters: None
	
	Description: This function turns on the green led
	
*/

void _greenled_turn_on(void)
{
	sbi(DDRC,OUT_LED_GN_PC1);
	sbi(PORTC,OUT_LED_GN_PC1);
	
	// Set the status of the green led to true
	sbi(wocket_status, BIT2_GREENLED_STATUS); 
}


/* 
	Function Name: _greenled_turn_off
	Parameters: None
	
	Description: This function turns off the green led
	
*/

void _greenled_turn_off(void)
{
	sbi(DDRC,OUT_LED_GN_PC1);
	cbi(PORTC,OUT_LED_GN_PC1);
	cbi(DDRC,OUT_LED_GN_PC1);
	
	// Set the status of the green led to false
	cbi(wocket_status, BIT2_GREENLED_STATUS);

}

/* 
	Function Name: _is_greenled_on
	Parameters: None
	
	Description: Tests if the green led is on
	
*/
unsigned char _is_greenled_on(void)
{
	return ((wocket_status>>BIT2_GREENLED_STATUS) & 0x01);
}


/* 
	Function Name:  _yellowled_turn_on
	Parameters: None
	
	Description: This function turns on the yellow led
	
*/
void _yellowled_turn_on(void)
{
	sbi(DDRC,OUT_LED_YE_PC2);
	sbi(PORTC,OUT_LED_YE_PC2);

	// Set the status of the yellow led to true
	sbi(wocket_status, BIT3_YELLOWLED_STATUS);
}

/* 
	Function Name:  _yellowled_turn_off
	Parameters: None
	
	Description: This function turns off the yellow led
	
*/
void _yellowled_turn_off(void)
{

	sbi(DDRC,OUT_LED_YE_PC2);
	cbi(PORTC,OUT_LED_YE_PC2);
	cbi(DDRC,OUT_LED_YE_PC2);	
	
	// Set the status of the yellow led to false
	cbi(wocket_status, BIT3_YELLOWLED_STATUS);
}

/* 
	Function Name: _is_yellowled_on
	Parameters: None
	
	Description: Tests if the yellow led is on
	
*/
unsigned char _is_yellowled_on(void)
{
	return ((wocket_status>>BIT3_YELLOWLED_STATUS) & 0x01);
}

void _atmega324p_init_uart0(unsigned int baud){
	/* Set baud rate */
	UBRR0H = (unsigned char)(baud>>8);
	UBRR0L = (unsigned char)baud;
	/* Enable receiver and transmitter */
	UCSR0B = (1<<TXEN0)|(1<<RXEN0);
	/* Set frame format: 8data, 2stop bit */
	//UCSR0C = (1<<USBS0)|(3<<UCSZ00);  //change 1 to 0 and &
	UCSR0C = (3<<UCSZ00);  //change 1 to 0 and &
}

void _atmega324p_init_uart1(unsigned int baud){
	/* Set baud rate */
	UBRR1H = (unsigned char)(baud>>8);
	UBRR1L = (unsigned char)baud;
	/* Enable receiver and transmitter */
	UCSR1B = (1<<RXEN1)|(1<<TXEN1);
	/* Set frame format: 8data, 2stop bit */
	UCSR1C =(3<<UCSZ10);  //change 1 to 0 and &
}




void _atmega324p_enable_free_running_adc(){
	   
   ADCSRB &= ~((1<<ADTS2) | (1<<ADTS1) | (1<<ADTS0)); //setting Free Running Mode
   ADCSRA |= (1 << ADATE);   //has to be set to 1 for ADC
}

void _atmega324p_disable_free_running_adc(){
	      
   ADCSRA &= ~(1 << ADATE);   //has to be set to 1 for ADC
}

void _atmega324p_set_prescalar_adc(unsigned char prescalar){
	if (prescalar==PRESCALAR_2){
		ADCSRA &= ~((1 << ADPS2) | (1 << ADPS1) | (1 << ADPS0));
	}else if (prescalar==PRESCALAR_4){
		ADCSRA &= ~((1 << ADPS2) | (1 << ADPS0));
		ADCSRA |= (1 << ADPS1);
	}else if (prescalar==PRESCALAR_8){
		ADCSRA &= ~(1 << ADPS2);
		ADCSRA |= ((1 << ADPS1) |(1 << ADPS0)) ;
	}else if (prescalar==PRESCALAR_16){
		ADCSRA &= ~((1 << ADPS1) |(1 << ADPS0));
		ADCSRA |= (1 << ADPS2);
	}else if (prescalar==PRESCALAR_32){
		ADCSRA &= ~(1 << ADPS1);
		ADCSRA |= ((1 << ADPS2)|(1 << ADPS0));
	}else if (prescalar==PRESCALAR_64){
		ADCSRA &= ~(1 << ADPS0);
		ADCSRA |= ((1 << ADPS2)|(1 << ADPS1));
	}else if (prescalar==PRESCALAR_128){		
		ADCSRA |= ((1 << ADPS2)|(1 << ADPS1)|(1 << ADPS0));
	}
}

//To do : add support to other than the internal
void _atmega324p_set_reference_adc(){
	ADMUX |=(1 << REFS0); // Set ADC reference to AVCC
}

void _atmega324p_enable_adc(){

	sbi(ADCSRA,ADEN);// power up

	//both the following are needed to allow ADIF to be set when a conversion completes
	//sbi(ADCSRA,ADIE);//enable ADC conversion interrupts  
	//sei(); //sets the I bit in the SREG 
}

void _atmega324p_disable_adc(){
	cbi(ADCSRA,ADEN);// power down
	//cbi(ADCSRA,ADIE);//disable interrupts
}

void _atmega324p_start_adc(){
	sbi(ADCSRA, ADIF);   // clear hardware "conversion complete" flag 
	sbi(ADCSRA,ADSC);
}

//ADSC is 1 while converting, 0 when it is done.
unsigned char _atmega324p_is_complete_adc(){
	return bit_is_set(ADCSRA, ADSC);
}

void _atmega324p_set_channel_adc(unsigned char channel){
	if (channel==ADC0){
		cbi(ADMUX,0);
		cbi(ADMUX,1);
		cbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}
	else if (channel==ADC1){
		sbi(ADMUX,0);
		cbi(ADMUX,1);
		cbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}else if (channel==ADC2){
		cbi(ADMUX,0);
		sbi(ADMUX,1);
		cbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}else if (channel==ADC3){
		sbi(ADMUX,0);
		sbi(ADMUX,1);
		cbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}else if (channel==ADC4){
		cbi(ADMUX,0);
		cbi(ADMUX,1);
		sbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}else if (channel==ADC6)
	{
		cbi(ADMUX,0);
		sbi(ADMUX,1);
		sbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}
	else if (channel==ADC7)
	{
		sbi(ADMUX,0);
		sbi(ADMUX,1);
		sbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}
/*	else if (channel==ADC3){
		sbi(ADMUX,0);
		sbi(ADMUX,1);
		cbi(ADMUX,2);
		cbi(ADMUX,3);
		cbi(ADMUX,4);
	}*/
}

unsigned short _atmega324p_a2dConvert10bit(unsigned char channel){
	//select channel
	_atmega324p_set_channel_adc(channel);
	_atmega324p_start_adc();
	while(_atmega324p_is_complete_adc()); 
	return ((ADCL)|((ADCH)<<8));
}
void _atmega324p_init_adc(){

	//set the directional pins for the A/D converter
	cbi(DDRA,X_PIN);
	cbi(DDRA,Y_PIN);
	cbi(DDRA,Z_PIN);
	cbi(DDRA,6);
	 _atmega324p_set_reference_adc();	
  // 	ADMUX |= (1 << REFS0); // Set ADC reference to AVCC
  	//ADMUX |= (1 << ADLAR); // Left adjust ADC result to allow easy 8 bit reading
   // No MUX values needed to be changed to use ADC0
   //ADCSRA |= (1 << ADATE);   //has to be set to 1 for ADC
   //ADCSRB &= (0<<ADTS2) | (0<<ADTS1) | (0<<ADTS0); //setting Free Running Mode
	
	//_atmega324p_enable_free_running_adc();
	_atmega324p_set_prescalar_adc(PRESCALAR_64);
   //ADCSRA |= (0 << ADPS2) | (1 << ADPS1) | (1 << ADPS0); // Set ADC prescalar to 8 - 125KHz sample rate @ 1MHz
   //Set prescalar to 64 -125 KHZ rate @ 8MHz
	_atmega324p_enable_adc();


	//set LED PINs
	sbi(DDRC,GREEN_LED);
	sbi(DDRC,YELLOW_LED);
  // ADCSRA |= (1 << ADSC);  // Start A2D Conversions
  //_atmega324p_start_adc();

}

void _atmega324p_green_led_on(){
	sbi(PORTC,GREEN_LED);
}

void _atmega324p_green_led_off(){
	cbi(PORTC,GREEN_LED);
}


void _atmega324p_yellow_led_on(){
	sbi(PORTC,YELLOW_LED);
}

void _atmega324p_yellow_led_off(){
	cbi(PORTC,YELLOW_LED);
}


void _atmega324p_powerdown(){
SMCR = 0x05;
}

void _atmega324p_disable_JTAG(void)
//by default the interface is enabled to disable it JTD has to be written logic 1
	// 2 times in 4 cycles.
{
	unsigned char sreg;

	sreg = SREG;
	cli();
	MCUCR |= ( 1 <<JTD );
	MCUCR |= ( 1 <<JTD );
	SREG = sreg;
}


unsigned char ReceiveByte(unsigned char *data)
  {
  	int count=0;
   while ( !(UCSR0A &  (1<<RXC0)) )
   {
   		if (count++==1) return 1; //timed out
   			_delay_ms(1);
   }     /*  Wait for incoming data   */

   *data=UDR0;

   return 0;/* Return success*/
  }


void TransmitByte( unsigned char data )
{
  while ( !(UCSR0A & (1<<UDRE0)) );        /* Wait for   empty transmit buffer */
  UCSR0A=UCSR0A & 0xdf;
  
  UDR0 =  data;  /* Start transmission   */
   
}

unsigned char _atmega324p_shutdown(){

        return (0x01 & (PINA>>USER_BUTTON_PIN));


}


void _atmega324p_power_down()
{
	set_sleep_mode(SLEEP_MODE_PWR_DOWN);
	sleep_enable();
	sleep_mode();	
}


void _atmega324p_reset()
{		
        cli(); //irq's off
        wdt_enable(WDTO_15MS); //wd on,15ms
        while(1); //loop 
}


//unsigned char i;
//unsigned char r;
//char buffer[8];
//unsigned short adc_result;
unsigned long delta;
void _atmega324p_init(unsigned int baud){

	//disable JTAG interface	
	_atmega324p_disable_JTAG();

//	r=0;

	//initialize UART0, connected to the RX of the BT
	_atmega324p_init_uart0(baud);
//	_atmega324p_init_uart1(baud);

	//set the BT
	_rn41_init();

    //initialize the accelerometer settings
	_mma7260qt_init();

	//initialize the digital to analog converter
	_atmega324p_init_adc();


	//set user button as input
        cbi(DDRA,USER_BUTTON_PIN);
        sbi(PINA,USER_BUTTON_PIN);


	//power save mode

	SMCR |=((1<<SM0)|(1<<SM1) | (1<<SE));

	//timer setup timer/counter2

	 TCCR2B |= ((1 << CS20) |(1 << CS21) | (1 << CS22)); // Set up timer 
	 TCNT2=154;
	 TIMSK2 |= (1 << TOIE2); // Enable CTC interrupt
   	 sei(); //  Enable global interrupts 

	
}




