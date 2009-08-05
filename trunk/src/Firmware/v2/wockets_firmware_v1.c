#include "avr_general.h"
#include "mcu_atmega324p.h"
#include "acc_mma7260qt.h"
#include "bt_rn41.h"
#include "crc.h"
#include "encoder.h"
#include "wockets_commands.h"
#include <util/delay.h>
#include <stdlib.h>
#include <avr/io.h>
#include <avr/interrupt.h>
#include <avr/sleep.h>
#include <avr/eeprom.h> 


unsigned short adc_result[5];
unsigned char buffer[MAX_COMMAND_SIZE];
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
unsigned int disconnection_counter=0;

unsigned char battery;

unsigned char aByte=0;
unsigned int alive_timer=0;
unsigned char response=0;
unsigned char opcode=0;
int command_counter=0;
int receive_counter=0;

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
	
    for(;;)  {            /* Forever */
	 sleep_enable();	
	}  

	return 0;
}


ISR(TIMER2_OVF_vect){

		//When the counter wraps around the timer
		TCNT2=170;
		if (sleep==0){
			 if (_rn41_is_connected()){
				_atmega324p_yellow_led_off();
				if (led_counter==1)
					_atmega324p_green_led_on();
				else if (led_counter==10)
					_atmega324p_green_led_off();
				else if (led_counter==600)
					led_counter=0;	
				sleep_counter=0;
				sleep_counter2=0;

		
				/* Receive and process any commands */
				if (ReceiveByte(&aByte)==0)
				{
					opcode=aByte&0x1f;
					switch (opcode)
					{
						case (unsigned char)ALIVE:							
							alive_timer=0;							
							break;
					    case (unsigned char) GET_BATTERY_LEVEL:
							adc_result[ADC4]=_atmega324p_a2dConvert10bit(ADC4);
							response=RESPONSE_HEADER | BATTERY_LEVEL_RESPONSE ;							
							TransmitByte(response);							
							response=(adc_result[ADC4]>>3);
							TransmitByte(response);							
							response=(adc_result[ADC4] & 0x07)<<4;
							TransmitByte(response);
							break;
						case (unsigned char) SET_CALIBRATION_VALUES:
							/*command_counter=0;
							receive_counter=0;
							buffer[command_counter]=aByte;							
							while (receive_counter<100){
								if (ReceiveByte(&aByte)==0){
									buffer[command_counter]=aByte;	
									command_counter++;
									if (command_counter==10){
										//save calibration data in non-volatile memoery
										break;
									}
								}
								receive_counter++;								
							}*/
							break;
						case (unsigned char) GET_CALIBRATION_VALUES:	
						
							//write one word each iteration
							while (!eeprom_is_ready());
							eeprom_write_word((uint16_t *)0x0,25);
							
							/*eeprom_write_word((uint16_t *)0x2,25);
							eeprom_write_word((uint16_t *)0x4,25);
							eeprom_write_word((uint16_t *)0x6,25);
							eeprom_write_word((uint16_t *)0x8,25);
							eeprom_write_word((uint16_t *)0x10,25);
						
/*							response=RESPONSE_HEADER | CALIBRATION_VALUES_RESPONSE;							
							TransmitByte(response);							
							response=;
							TransmitByte(response);							
							response=(adc_result[ADC4] & 0x07)<<4;
							TransmitByte(response);
							*/
							break;					
						default:	
							break;

					}    
																			
				}

          
				alive_timer++;					
				if (alive_timer>=	3000) //if no acks for approx 30 seconds, reset radio
				{
					_rn41_reset();
					alive_timer=0;
					//_delay_ms(10000);
				}
					 
					
				adc_result[ADC1]=_atmega324p_a2dConvert10bit(ADC1);
				adc_result[ADC2]=_atmega324p_a2dConvert10bit(ADC2);
				adc_result[ADC3]=_atmega324p_a2dConvert10bit(ADC3);
				
				//tag if close to ack
				if (ack==0xff)
					TransmitFrame(encode(1,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));
				else  //otherwise dont tag
					TransmitFrame(encode(0,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));

			}else{

				_atmega324p_green_led_off();
				if (led_counter==1)
					_atmega324p_yellow_led_on();
				else if (led_counter==10)
					_atmega324p_yellow_led_off();
				else if (led_counter==600)
					led_counter=0;                
				sleep_counter++;

				if (sleep_counter>=14400)
				{
					sleep_counter=0;
					sleep_counter2++;					

				}
				if (sleep_counter2>30)
				{
					sleep=1;													
					_atmega324p_yellow_led_off();
					_rn41_off();
					_mma7260qt_sleep();		
					_atmega324p_power_down();
				}
			}

				led_counter++;	
		}

}

