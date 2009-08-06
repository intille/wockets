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
unsigned char opcode=0;
unsigned char command_counter=0;
unsigned char command_length=0;
unsigned char command_timer=0;
unsigned char processed_counter=0;

unsigned int alive_timer=0;
unsigned char response=0;
int receive_counter=0;
unsigned char aCommand[MAX_COMMAND_SIZE];
unsigned short word=0;
unsigned short charge=0;
unsigned int address=0;

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


		
				/* Receive commands */
				if (ReceiveByte(&aByte)==0)
				{				
					aCommand[command_counter++]=aByte;
					if (command_counter==1)
					{
						opcode=aByte&0x1f;

						//Depending on the opcode set the expected command length
						switch (opcode)
						{
								case (unsigned char)GET_BATTERY_LEVEL:
								case (unsigned char)GET_PACKET_COUNT:
								case (unsigned char)GET_SENSOR_SENSITIVITY:
								case (unsigned char)GET_CALIBRATION_VALUES:
								case (unsigned char)GET_SAMPLING_RATE:
								case (unsigned char)GET_ALIVE_TIMER:
								case (unsigned char)GET_POWER_DOWN_TIMER:
								case (unsigned char)RESET_WOCKET:
								case (unsigned char)GET_BAUD_RATE:
								case (unsigned char)ALIVE:
									command_length=1;
									break;
								case (unsigned char)SET_LED:
								case (unsigned char)SET_SENSOR_SENSITIVITY:		
								case (unsigned char)SET_SAMPLING_RATE:
								case (unsigned char)SET_ALIVE_TIMER:
								case (unsigned char)SET_POWER_DOWN_TIMER:
								case (unsigned char)SET_BAUD_RATE:						
									command_length=2;
									break;
								case (unsigned char)SET_CALIBRATION_VALUES:
									command_length=10;
									break;								

						}
						command_timer=0;
					}

				}

				if (command_counter>0)
					command_timer++;

				//if command timer started and command fully received
				if ((command_timer>0) && (command_length==command_counter))
				{
					switch (opcode)
					{
						case (unsigned char)ALIVE:							
							alive_timer=0;
							processed_counter=command_counter;							
							break;
					    case (unsigned char) GET_BATTERY_LEVEL:
							adc_result[ADC4]=_atmega324p_a2dConvert10bit(ADC4);
							response=RESPONSE_HEADER | BATTERY_LEVEL_RESPONSE ;							
							TransmitByte(response);							
							response=(adc_result[ADC4]>>3);
							TransmitByte(response);							
							response=(adc_result[ADC4] & 0x07)<<4;
							TransmitByte(response);
							processed_counter=command_counter;
							break;
						case (unsigned char) SET_CALIBRATION_VALUES:							
							//if eeprom is ready
							if (eeprom_is_ready()){
								//read the charge if needed
								if (charge==0)
									charge=_atmega324p_a2dConvert10bit(ADC4);								
								if (charge>350)
								{								
									if (processed_counter==0){											
										word=(((unsigned short)(aCommand[1]&0x7f))<<3) | (((unsigned short)(aCommand[2]&0x70))>>4);
										address=X1G_ADDRESS;	
										processed_counter=2;																		
									}else if (processed_counter==2){											
										word=(((unsigned short)(aCommand[2]&0x0f))<<6) | (((unsigned short)(aCommand[3]&0x7e))>>1);
										address=X1NG_ADDRESS;	
										processed_counter=3;		
									}else if (processed_counter==3){											
										word=(((unsigned short)(aCommand[3]&0x01))<<9) | (((unsigned short)(aCommand[4]&0x7f))<<2)  | (((unsigned short)(aCommand[5]&0x60))>>5);
										address=Y1G_ADDRESS;	
										processed_counter=5;		
									}else if (processed_counter==5){											
										word=(((unsigned short)(aCommand[5]&0x1f))<<5) | (((unsigned short)(aCommand[6]&0x7c))>>2);
										address=Y1NG_ADDRESS;	
										processed_counter=6;		
									}else if (processed_counter==6){											
										word=(((unsigned short)(aCommand[6]&0x03))<<8) | (((unsigned short)(aCommand[7]&0x7f))<<1) | (((unsigned short)(aCommand[8]&0x40))>>6);
										address=Z1G_ADDRESS;	
										processed_counter=7;		
									}else if (processed_counter==7){											
										word=(((unsigned short)(aCommand[8]&0x3f))<<4) | (((unsigned short)(aCommand[9]&0x78))>>3);
										address=Z1NG_ADDRESS;	
										processed_counter=command_counter;		
									}
									cli();							
									eeprom_write_word((uint16_t *)address,word);
									sei();																	
								}
							}
							//enable global interrupts
							break;
						case (unsigned char) GET_CALIBRATION_VALUES:	
						
								if (eeprom_is_ready()){
								//read the charge if needed
								if (charge==0)
								{
									charge=_atmega324p_a2dConvert10bit(ADC4);
									address=X1G_ADDRESS;
									aCommand[0]=0xc4;
								}
								if (charge>350)
								{	
									cli();							
									word=eeprom_read_word((uint16_t *)address);
									sei();															
									if (address==X1G_ADDRESS){
										aCommand[1]= ((word>>3)&0x7f);									
										aCommand[2]= ((word<<4)&0x70);
										address=X1NG_ADDRESS;
									}else if (address==X1NG_ADDRESS){
										aCommand[2]|= ((word>>6)&0x0f);
										aCommand[3] =((word<<1)&0x7e);
										address=Y1G_ADDRESS;
									}else if (address==Y1G_ADDRESS){
										aCommand[3]|= ((word>>9) &0x01);
										aCommand[4] = ((word>>2) & 0x7f);
										aCommand[5] = ((word<<5) & 0x60);
										address=Y1NG_ADDRESS;
									}else if (address==Y1NG_ADDRESS){
										aCommand[5]|= ((word>>5) & 0x1f);
										aCommand[6] = ((word<<2) & 0x7c);
										address=Z1G_ADDRESS;
									}else if (address==Z1G_ADDRESS){
										aCommand[6] |= ((word>>8) & 0x03);
										aCommand[7] =((word>>1) & 0x7f);
										aCommand[8] = ((word<<6) & 0x40);
										address=Z1NG_ADDRESS;
									}else if (address==Z1NG_ADDRESS){
										aCommand[8] |= ((word>>4) & 0x3f);
										aCommand[9] = ((word<<3) & 0x78);
										processed_counter=command_counter;
										for (i=0;(i<10);i++)
											TransmitByte(aCommand[i]);																		
									}
																																							
																							
								}
							}
							break;					
						default:	
							break;

					}
					if (processed_counter==command_counter){
						command_length=0;
						command_counter=0;
						command_timer=0;
						processed_counter=0;
						charge=0;
						address=0;
					}
				} //if command timed out
				else if (command_timer==MAX_COMMAND_TIMER)
				{
							
					command_length=0;
					command_counter=0;
					command_timer=0;
					processed_counter=0;
					charge=0;
					address=0;
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

