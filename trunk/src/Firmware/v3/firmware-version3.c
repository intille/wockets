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

#include <avr/power.h>
#include "mcu_atmega.h"
#include "wocket.h"
#include <util/delay.h>

unsigned char wakeup=0;
unsigned char sample=0;


int main()
{
				
scounter=0;


	// Blink green for 5 seconds	

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

unsigned char interrupt_reps=0;

ISR(TIMER2_OVF_vect)
{
	/* Skip sampling depending on the sampling rate variables/timers */
 	if (interrupt_reps==0)
	{	
		interrupt_reps=_wTCNT2_reps;
		TCNT2=_wTCNT2;
	}
	else{ //otherwise wait
		if (interrupt_reps==1)	
			TCNT2=_wTCNT2_last;	
		else		
			TCNT2=_wTCNT2;					
		interrupt_reps--;
		return;
	}


	
	/* Sample data and transmt it if necessary */
	if (_wTM==_TM_Continuous)
	{
		if (!_bluetooth_is_connected())
		{
			if (_wPDT!=0){
				_wShutdownTimer--;
				if (_wShutdownTimer==0)
					_atmega_finalize();
			}
			return;		
		}

		if (_wShutdownTimer!=_DEFAULT_SHUTDOWN)
			_wShutdownTimer=_DEFAULT_SHUTDOWN;

		 _wPC++;

		power_adc_enable();
		_atmega_adc_turn_on();
		_receive_data();				
		_send_data();				
	}
	else if (_wTM==_TM_Burst_60)
	{
		if (_wPDT!=0)
			_wShutdownTimer--;

		 _wPC++;
		power_adc_enable();
		_atmega_adc_turn_on();
		xs[scounter]=_atmega_a2dConvert10bit(IN_ACCEL_X_FILT);
		ys[scounter]=_atmega_a2dConvert10bit(IN_ACCEL_Y_FILT);
		zs[scounter++]=_atmega_a2dConvert10bit(IN_ACCEL_Z_FILT);
		if (scounter>255)
			scounter=0;
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
		//reset shutdown timer if connected
		if ((_wPDT!=0) && (_wShutdownTimer!=_DEFAULT_SHUTDOWN))
			_wShutdownTimer=_DEFAULT_SHUTDOWN;

		connected=1;
		_receive_data();		
		_send_packet_count(2400);
		_send_data_bufferred();

		seconds_passed=0;
		while (seconds_passed<400)
		{
			_delay_ms(5);
			seconds_passed++;

		}
						
		_bluetooth_turn_off();		
		seconds_disconnected=0;
	}




}



