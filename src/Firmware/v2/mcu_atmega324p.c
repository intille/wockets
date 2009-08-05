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
#include <util/delay.h>
#include <stdlib.h>


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
	UCSR1B = (1<<TXEN1)|(1<<RXEN1);
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
	ADMUX |= (1 << REFS0); // Set ADC reference to AVCC
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
	 _atmega324p_set_reference_adc();	
  // 	ADMUX |= (1 << REFS0); // Set ADC reference to AVCC
  	//ADMUX |= (1 << ADLAR); // Left adjust ADC result to allow easy 8 bit reading
   // No MUX values needed to be changed to use ADC0
   //ADCSRA |= (1 << ADATE);   //has to be set to 1 for ADC
   //ADCSRB &= (0<<ADTS2) | (0<<ADTS1) | (0<<ADTS0); //setting Free Running Mode
	
	//_atmega324p_enable_free_running_adc();
	_atmega324p_set_prescalar_adc(PRESCALAR_8);
   //ADCSRA |= (0 << ADPS2) | (1 << ADPS1) | (1 << ADPS0); // Set ADC prescalar to 8 - 125KHz sample rate @ 1MHz
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

void _atmega324p_power_down()
{
	set_sleep_mode(SLEEP_MODE_PWR_DOWN);
	sleep_enable();
	sleep_mode();	
}


//unsigned char i;
//unsigned char r;
//char buffer[8];
//unsigned short adc_result;
unsigned long delta;
void _atmega324p_init(){

	//disable JTAG interface	
	_atmega324p_disable_JTAG();

//	r=0;

	//initialize UART0, connected to the RX of the BT
	_atmega324p_init_uart0( (unsigned int)12);

	//set the BT
	_rn41_init();

    //initialize the accelerometer settings
	_mma7260qt_init();

	//initialize the digital to analog converter
	_atmega324p_init_adc();


	//power save mode

	SMCR |=((1<<SM0)|(1<<SM1) | (1<<SE));

	//timer setup timer/counter2

	 TCCR2B |= ((1 << CS20) |(1 << CS21) | (1 << CS22)); // Set up timer 
	 TCNT2=154;
	 TIMSK2 |= (1 << TOIE2); // Enable CTC interrupt
   	 sei(); //  Enable global interrupts 

	
}



ISR(ADC_vect){
	/*  i=0;
	  r++;

	  	if (r==10){
	  
	    if (_mma7260qt_is_asleep()){
			TransmitByte('W');			
	    	_mma7260qt_wakeup();
		}else{
			
			TransmitByte('S');
			_mma7260qt_sleep();
		}

		if (!_rn41_is_discoverable()){
			TransmitByte('X');	
		}
		if (_rn41_is_connected()){
			TransmitByte('C');
		}
			r=0;	
		}
		  	

		PORTB=1;
        _delay_ms(1000);
		PORTB=0;
		_delay_ms(1000);


		 adc_result=((ADCL)|((ADCH)<<8));

		 */
// Dynamic Acceleration test

/*		 if (adc_result> previous_adc_result) {
		 difference = adc_result - previous_adc_result;}
		 else {
		 difference = previous_adc_result - adc_result;}
	     previous_adc_result = adc_result;


		 delta = delta + difference;

		 for(i=0;(i<6);i++)
		 	buffer[i]=0;
		 itoa(delta,buffer,10);
		 for(i=0;(i<6);i++)		 	
		 	TransmitByte(buffer[i]); 
*/


 		 //Static acceleration test

	/*	 for(i=0;(i<4);i++)
		 	buffer[i]=0;
		 itoa(adc_result,buffer,10);
		 for(i=0;(i<4);i++)		 	
		 	TransmitByte(buffer[i]);
			

         TransmitByte(',');
		  delta=0;
 	 
	 _delay_ms(100);
	 */
}

