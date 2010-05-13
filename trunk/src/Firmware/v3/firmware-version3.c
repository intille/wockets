//*****************************************************************************
//
// File Name    : 'firmware-version3.c'
// Title        : Interrupt driven code for the wockets
// Author       : Fahd Albinali
// Created      : 12/10/2008
// Modified     : 03/18/2010
// 
//  Description : This file includes the main loop for the code that runs on the wocket and
//  any interrupt service routines (ISRs). The code supports a variety of configuration modes
//  for the wockets including Master/Slave modes and supports low and high power configurations                 
//
// This code is distributed under the MIT License
//     
//
//*****************************************************************************

#include <stdlib.h>
#include <avr/io.h>
#include <avr/wdt.h>
#include <avr/interrupt.h>
#include <avr/sleep.h>
#include <avr/eeprom.h> 
#include <util/delay.h>
#include <avr/power.h>
#include "mcu_atmega.h"
#include "wocket.h"

unsigned char wakeup=0;
unsigned char sample=0;
int main()
{


	_wocket_initialize();
		

	power_adc_disable();
  	power_spi_disable();
  	power_timer0_disable();
  	power_timer1_disable();
  	power_twi_disable();



	while(1){
			
			cli();
			set_sleep_mode(SLEEP_MODE_IDLE);
			//set_sleep_mode(SLEEP_MODE_PWR_SAVE);
    		sleep_enable();
    		sleep_bod_disable(); 	
    		sei();
    		sleep_cpu();
    		sleep_disable();


	}

	return 0;
}



/* Interrupt Service Routines */
unsigned int seconds_passed=0;
unsigned int counter=0;

unsigned char skip_interrupt_counter=0;
unsigned char connected=0;
unsigned int seconds_disconnected=0;

unsigned short configurationTimer=1;
unsigned char interrupts_passed=0;


ISR(TIMER2_OVF_vect)
{

/*
	TCNT2=61;

		if (!_bluetooth_is_connected())	
		return;	

	wakeup=0;
	sample=0;


	_receive_data();	
	power_adc_enable();

	_atmega_adc_turn_on();
	_send_data();
	_atmega_adc_turn_off();
	power_adc_disable();


	seconds_disconnected=0;
	*/



	TCNT2=61;
	
	power_adc_enable();
	_atmega_adc_turn_on();
	unsigned short x=_atmega_a2dConvert10bit(ADC3);
	unsigned short y=_atmega_a2dConvert10bit(ADC2);
	unsigned short z=_atmega_a2dConvert10bit(ADC1);
	_atmega_adc_turn_off();
	power_adc_disable();

	



	if (!_bluetooth_is_connected()){
			
		if (seconds_disconnected<1800)
			seconds_disconnected++;
		else if (seconds_disconnected==1800)
		{
			_bluetooth_turn_on();
			//_atmega_reset();
			seconds_disconnected=1801;			
		}
		return;	

	}
		
		//_atmega_adc_turn_on();
		connected=1;
		//parse and process any received bytes

		//if (seconds_passed==0){
			_receive_data();
		//	 _send_data();
		//_send_packet_count(600);
	
		_send_packet_count(1200);
		_send_data_bufferred();

			seconds_passed=0;
			while (seconds_passed<400)
			{
				_delay_ms(5);
				seconds_passed++;

			}
			
			
			_bluetooth_turn_off();
		//	_atmega_adc_turn_off();
			seconds_disconnected=0;

}



