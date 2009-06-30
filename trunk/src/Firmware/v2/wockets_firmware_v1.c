#include "avr_general.h"
#include "mcu_atmega324p.h"
#include "acc_mma7260qt.h"
#include "bt_rn41.h"
#include "crc.h"
#include "encoder.h"
#include <util/delay.h>
#include <stdlib.h>
#include <avr/io.h>
#include <avr/interrupt.h>
#include <avr/sleep.h>
#define CHANNELID 15
unsigned short adc_result[5];
char buffer[8];
unsigned char i;
unsigned char r;
unsigned char j;
unsigned char ack;
unsigned char crcval=0;
unsigned int seq_num;

unsigned int led_counter=0;
unsigned int sleep_counter=0;
unsigned int sleep_counter2=0;
unsigned int sleep=0;
unsigned int ack_timer=0;
unsigned int disconnection_counter=0;

unsigned char battery;


void TransmitFrame(WOCKETS_UNCOMPRESSED_FRAME f){
	
	TransmitByte(f.byte1);
	TransmitByte(f.byte2);
	TransmitByte(f.byte3);
	TransmitByte(f.byte4);
	TransmitByte(f.byte5);
	
}




int main()
{
	_atmega324p_init();
	
	led_counter=1;
	_rn41_on();
	_mma7260qt_wakeup();

	//setup the timer interrupt
	//scaling 256 and counter
    for(;;)  {            /* Forever */

	 sleep_enable();
	
/*
		if (sleep==0){
			 if (_rn41_is_connected()){
				_atmega324p_yellow_led_off();
				if (led_counter==1)
					_atmega324p_green_led_on();
				else if (led_counter==25)
					_atmega324p_green_led_off();
				else if (led_counter==100)
					led_counter=0;	
				sleep_counter=0;
				sleep_counter2=0;

		
				ack=ReceiveByte();				
				if (ack==0xff)
					ack_timer=0;
                else if (ack==0xA0)
				{
					adc_result[ADC4]=_atmega324p_a2dConvert10bit(ADC4);
					battery=0xC0;
					TransmitByte(battery);
					battery=adc_result[ADC4];
					battery=battery>>3;
					TransmitByte(battery);
					battery=adc_result[ADC4];
					battery=(battery &0x07)<<4;
					TransmitByte(battery);
				}            
				ack_timer++;					
				if (ack_timer>=	3000) //if no acks for approx 30 seconds, reset radioo	
				{
					_rn41_reset();
					ack_timer=0;
					//_delay_ms(10000);
				}
					
					
				adc_result[ADC1]=_atmega324p_a2dConvert10bit(ADC1);
				adc_result[ADC2]=_atmega324p_a2dConvert10bit(ADC2);
				adc_result[ADC3]=_atmega324p_a2dConvert10bit(ADC3);
				TransmitFrame(encode(sensitivity,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));
		

			}else{

				_atmega324p_green_led_off();
				if (led_counter==1)
					_atmega324p_yellow_led_on();
				else if (led_counter==25)
					_atmega324p_yellow_led_off();
				else if (led_counter==600)
					led_counter=0;                
				sleep_counter++;

				if (sleep_counter>=14400)
				{
					sleep_counter=0;
					sleep_counter2++;					

				}
				if (sleep_counter2>10)
				{
					sleep=1;													
					_atmega324p_yellow_led_off();
					_rn41_off();
					_mma7260qt_sleep();		
					_atmega324p_power_down();
				}
			}

				led_counter++;	

		   		_delay_ms(10);
		}else{
			_delay_ms(10000);
		}
		*/
	}  

	return 0;
}


ISR(TIMER2_OVF_vect){


		if (sleep==0){
			 if (_rn41_is_connected()){
				_atmega324p_yellow_led_off();
				if (led_counter==1)
					_atmega324p_green_led_on();
				else if (led_counter==25)
					_atmega324p_green_led_off();
				else if (led_counter==100)
					led_counter=0;	
				sleep_counter=0;
				sleep_counter2=0;

		
				ack=ReceiveByte();				
				if (ack==0xff)
					ack_timer=0;
                else if (ack==0xA0)
				{
					adc_result[ADC4]=_atmega324p_a2dConvert10bit(ADC4);
					battery=0xC0;
					TransmitByte(battery);
					battery=adc_result[ADC4];
					battery=battery>>3;
					TransmitByte(battery);
					battery=adc_result[ADC4];
					battery=(battery &0x07)<<4;
					TransmitByte(battery);
				}            
				ack_timer++;					
				if (ack_timer>=	3000) //if no acks for approx 30 seconds, reset radioo	
				{
					_rn41_reset();
					ack_timer=0;
					//_delay_ms(10000);
				}
					
					
				adc_result[ADC1]=_atmega324p_a2dConvert10bit(ADC1);
				adc_result[ADC2]=_atmega324p_a2dConvert10bit(ADC2);
				adc_result[ADC3]=_atmega324p_a2dConvert10bit(ADC3);
				TransmitFrame(encode(sensitivity,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));
		

			}else{

				_atmega324p_green_led_off();
				if (led_counter==1)
					_atmega324p_yellow_led_on();
				else if (led_counter==25)
					_atmega324p_yellow_led_off();
				else if (led_counter==600)
					led_counter=0;                
				sleep_counter++;

				if (sleep_counter>=14400)
				{
					sleep_counter=0;
					sleep_counter2++;					

				}
				if (sleep_counter2>10)
				{
					sleep=1;													
					_atmega324p_yellow_led_off();
					_rn41_off();
					_mma7260qt_sleep();		
					_atmega324p_power_down();
				}
			}

				led_counter++;	

		   	//	_delay_ms(10);
		}else{
			_delay_ms(10000);
		}
	TCNT2=154;
}

