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
#include <math.h>
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


unsigned short x;
unsigned short y;
unsigned short z;
unsigned short b;


unsigned long xs[900];
unsigned long ys[900];
unsigned long zs[900];
unsigned long bs[900];
double xmean;
double ymean;
double zmean;
double bmean
;
double xsum;
double ysum;
double zsum;
double bsum;


unsigned short dataIndex;
unsigned char dataSubindex;
unsigned char sampleFlag=0;
unsigned short batch_counter=0;

/* Interrupt Service Routines */
unsigned int seconds_passed=0;
unsigned int counter=0;

unsigned char skip_interrupt_counter=0;
unsigned char connected=0;
unsigned int seconds_disconnected=0;

unsigned short configurationTimer=1;
unsigned char interrupts_passed=0;

unsigned char interrupt_reps=0;



int main()
{
				
scounter=0;


	//Initialized data buffer
	dataIndex=0;
	// Blink green for 5 seconds	

	_wocket_initialize();
		

	power_adc_disable();
  	power_spi_disable();
  	power_timer0_disable();
  	power_timer1_disable();
  	power_twi_disable();
	xmean=0;
	ymean=0;
	zmean=0;
	xsum=0;
	ysum=0;
	zsum=0;
	sampleFlag=1;


	while(1){
			

			if (connected)
				break;

		//Sample only in the main loop because of p
		if(sampleFlag){
			power_adc_enable();
			_atmega_adc_turn_on();

			x=_atmega_a2dConvert10bit(ADC2);
			y=_atmega_a2dConvert10bit(ADC1);
			z=_atmega_a2dConvert10bit(ADC0);
			b=_atmega_a2dConvert10bit(ADC7);
	
			xs[dataIndex]=x;
			ys[dataIndex]=y;
			zs[dataIndex]=z;
			bs[dataIndex]=b;

			xmean+=x;
			ymean+=y;
			zmean+=z;
			bmean+=b;


			dataIndex++;				 

			//Compute the noise level
			if (dataIndex==900)
			{
				xmean/=900.0;
				ymean/=900.0;
				zmean/=900.0;
				bmean/=900.0;

				for (dataIndex=0;(dataIndex<900);dataIndex++)
				{
					xs[dataIndex]=(xs[dataIndex]-xmean)*(xs[dataIndex]-xmean);
					ys[dataIndex]=(ys[dataIndex]-ymean)*(ys[dataIndex]-ymean);
					zs[dataIndex]=(zs[dataIndex]-zmean)*(zs[dataIndex]-zmean);
					bs[dataIndex]=(bs[dataIndex]-bmean)*(bs[dataIndex]-bmean);
					
					xsum+=xs[dataIndex];
					ysum+=ys[dataIndex];
					zsum+=zs[dataIndex];
					bsum+=bs[dataIndex];

				}

				xsum=sqrt(xsum/900);
				ysum=sqrt(ysum/900);
				zsum=sqrt(zsum/900);
				bsum=sqrt(bsum/900);


				if ( (xsum>3) || (ysum>3) || (zsum>3) || (xsum==0) || (ysum==0) || (zsum==0))
				{

					while(1)
					{
						_yellowled_turn_on();		
						for(int i=0;(i<200);i++)
							_delay_ms(5);
						_yellowled_turn_off();
						for(int i=0;(i<200);i++)
							_delay_ms(5);
					}			

				}

				if (bsum>1)
					_yellowled_turn_on();
				
				_greenled_turn_on();
				//_atmega_finalize();


			}
			 //Most of the time the data buffer with 750 will not overflow
			 //and will be enough to transmit the data, data will go from 0 up to a specific
			 //value

			_atmega_adc_turn_off();
			power_adc_disable();

			sampleFlag=0;
		}	
		
		_yellowled_turn_off();
		_greenled_turn_on();
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






ISR(TIMER2_OVF_vect)
{

	/* If the wocket is docked in shut it down */

//	if (_is_docked())
//		_atmega_finalize();
		
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
	sampleFlag=1;
	if (_wTM==_TM_Continuous)
		 _wPC++;	
	else if (_wTM==_TM_Burst_60)
	{
		if (_wPDT!=0)
			_wShutdownTimer--;

		 _wPC++;

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

		_atmega_finalize();
		connected=1;
		_receive_data();		
		/*_send_batch_count(2400);
		_send_data_bufferred();

		seconds_passed=0;
		while (seconds_passed<400)
		{
			_delay_ms(5);
			seconds_passed++;

		}
						
		_bluetooth_turn_off();		
		seconds_disconnected=0;*/
	}




}



