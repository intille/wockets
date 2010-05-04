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

unsigned char wakeup=0;
unsigned char sample=0;
int main()
{


	_wocket_initialize();
		
	while(1){
	
		if (!wakeup){
			set_sleep_mode(SLEEP_MODE_PWR_SAVE);
    		sleep_enable();
    		sleep_bod_disable();
    		sei();
    		sleep_cpu();
    		sleep_disable();
		}else
			_delay_ms(10);

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
	if (!_bluetooth_is_connected())	
		return;		

TCNT2=170;
	if (!sample){
		if (wakeup){
			TCNT2 = 246;
			sample=1;
		}else{
			TCNT2=180;	
			wakeup=1;			
		}
		return;
	}
	
	wakeup=0;
	sample=0;

	

	_receive_data();
	_send_data();
	
	seconds_disconnected=0;

		
	/*TCNT2=170;	


	if (!_bluetooth_is_connected()){
			
		if (seconds_disconnected<2400)
			seconds_disconnected++;
		else if (seconds_disconnected==2400)
		{
			_bluetooth_turn_on();
			//_atmega_reset();
			seconds_disconnected=2401;			
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

*/
}



