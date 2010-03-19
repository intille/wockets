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
#include "mcu_atmega.h"
#include "wocket.h"

int main()
{


	_wocket_initialize();
		
	while(1){
	
	/*	set_sleep_mode(SLEEP_MODE_PWR_SAVE);
    	sleep_enable();
    	sleep_bod_disable();
    	sei();
    	sleep_cpu();
    	sleep_disable();*/
		_delay_ms(10);

	}

	return 0;
}



/* Interrupt Service Routines */
unsigned int seconds_passed=0;
unsigned int counter=0;

unsigned char skip_interrupt_counter=0;


ISR(TIMER2_OVF_vect){ 

		TCNT2=170;	
		
	if (!_bluetooth_is_connected())
		{
			// Turn off peripherals that are not needed
		/*	_accelerometer_turn_off();
			_greenled_turn_off();
			_yellowled_turn_off();
			skip_interrupt_counter=0;*/
			return;
		}
		
		
		skip_interrupt_counter++;

		if (skip_interrupt_counter<num_skipped_timer_interrupts)
			return;
		
		skip_interrupt_counter=0;					

		//unsigned short x=_atmega_a2dConvert10bit(ADC3);
		//unsigned short y=_atmega_a2dConvert10bit(ADC2);
		//unsigned short z=_atmega_a2dConvert10bit(ADC1);
		_transmit_packet(_encode_packet(400,300,600));

		

		if (seconds_passed<20)
		{
			seconds_passed++;			
			return;
		}
		
		seconds_passed=0;
		if (_is_greenled_on())
			_greenled_turn_off();
		else
			_greenled_turn_on();

				
		/*if (_bluetooth_off)					
			_bluetooth_turn_on();								
		else					
			_bluetooth_turn_off();*/

		/*if (_is_accelerometer_on())
		{
			_accelerometer_set_sensitivity(_4G);
			_accelerometer_turn_on();
		}
		else
			_accelerometer_turn_off();
			*/
		/*if (_is_greenled_on())
			_greenled_turn_off();
		else
			_greenled_turn_on(); */

		/*if (_is_yellowled_on())
			_yellowled_turn_off();
		else
			_yellowled_turn_on();
	

		seconds_passed=0;	

		if (counter>5)
			_atmega_finalize();*/
}



