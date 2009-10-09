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
#include <avr/wdt.h>
#include <avr/interrupt.h>
#include <avr/sleep.h>
#include <avr/eeprom.h> 


unsigned short adc_result[5];
//unsigned char buffer[MAX_COMMAND_SIZE];
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
unsigned int command_timer=0;
unsigned char processed_counter=0;

unsigned int alive_timer=0;
unsigned char response=0;
int receive_counter=0;
unsigned char aBuffer[MAX_COMMAND_RESPONSE_SIZE];
unsigned short word=0;
unsigned short address=0xffff;
unsigned char response_length=0;
unsigned char disconnected_reset=1;
unsigned short sequence=0;


void TransmitFrame(WOCKETS_UNCOMPRESSED_FRAME f){
	
	TransmitByte(f.byte1);
	TransmitByte(f.byte2);
	TransmitByte(f.byte3);
	TransmitByte(f.byte4);
	TransmitByte(f.byte5);
	
}




int main()
{
	//disable watchdog to avoid reset
	MCUSR = 0;
	wdt_disable();
	
	word=eeprom_read_word((uint16_t *)((uint16_t)BAUD_RATE_ADDRESS));
	if (word==BAUD_9600)
		word=ATMEGA324P_BAUD_9600;
	else if (word==BAUD_19200)
		word=ATMEGA324P_BAUD_19200;
	else if (word==BAUD_28800)
		word=ATMEGA324P_BAUD_28800;
	else if (word==BAUD_38400)
		word=ATMEGA324P_BAUD_38400;
	else if (word==BAUD_57600)
		word=ATMEGA324P_BAUD_57600;
	else
	{
		word=ATMEGA324P_BAUD_38400;
		eeprom_write_word((uint16_t *)BAUD_RATE_ADDRESS,BAUD_38400);
	}	
	_atmega324p_init(word);
	_atmega324p_green_led_off();

	led_counter=0;
	_rn41_on();
	_mma7260qt_wakeup();
	

	
	
    while(sleep==0)  {            /* Forever */
	 	 
	 //set_sleep_mode(SLEEP_MODE_PWR_SAVE);
	 //sleep_enable();
	 //MCUCR = 0x60;            // Disable BOD during sleep to reduce power consumption (used to monitor supply voltage) 
   	 //MCUCR = 0x40;
	 //sleep_cpu();     
	 //sleep_disable();
	 	_delay_ms(5);
		if (!_atmega324p_shutdown())
			sleep=1;		 

		led_counter++;
		if (_rn41_is_connected()){
			_atmega324p_yellow_led_off();
			if (led_counter==1)
					_atmega324p_green_led_on();
			else if (led_counter==2)
				_atmega324p_green_led_off();
			else if (led_counter>=2000)
				led_counter=0;	
		}else{	 				
			if (led_counter==1)
				_atmega324p_yellow_led_on();
			else if (led_counter==2)
				_atmega324p_yellow_led_off();
			else if (led_counter>=2000)
				led_counter=0;    
		}           
	 
	}  

	//shutdown to minimize power
	//_atmega324p_reset();
	//make sure watchdog timer is disabled
	MCUSR = 0;
	wdt_disable();

	cli();
	TIMSK2=0;	
	_atmega324p_yellow_led_off();
	_atmega324p_green_led_on();
	_rn41_off();	
	_mma7260qt_sleep();	
	sleep_enable();	
	set_sleep_mode(SLEEP_MODE_PWR_SAVE);
	sleep_cpu();


	//won't be executed as long as the power save is entered correctly
	_atmega324p_yellow_led_on();
	_atmega324p_green_led_on();

	return 0;
}


ISR(TIMER2_OVF_vect){

		//When the counter wraps around the timer
		TCNT2=170;

		if (sleep==0){

			 if (_rn41_is_connected()){

				sleep_counter=0;
				sleep_counter2=0;
				disconnected_reset=0;
		
				/* 	Receive a byte on each timer interrupt only if no command is being received or
					if a command has been received in full */
				if ( ((command_counter==0)||(command_counter<command_length))  && (ReceiveByte(&aByte)==0) )
				{				
					aBuffer[command_counter++]=aByte;

					//for the first byte set the opcode and set the commands length and reset timer
					if ((aByte>>5)==COMMAND_PREFIX)
					{
						opcode=aByte&0x1f;						
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
						command_counter=1;
						command_timer=0;
						processed_counter=0;						
						address=0xffff;
						response_length=0;
					}

				}

				// increment timer as long as the command is still being received
				if (command_counter>0)
					command_timer++;

				//if all command is received, start processing it
				if ((command_counter>0) && (command_counter==command_length))
				{					
					switch (opcode)
					{
						//reset alive timer if it is alive
						case (unsigned char)ALIVE:							
							alive_timer=0;
							processed_counter=command_counter;							
							break;
						//setup battery buffer
					    case (unsigned char) GET_BATTERY_LEVEL:		
							word=_atmega324p_a2dConvert10bit(ADC4);
							aBuffer[0]=m_BATTERY_LEVEL_BYTE0;
							aBuffer[1]=m_BATTERY_LEVEL_BYTE1(word);
							aBuffer[2]=m_BATTERY_LEVEL_BYTE2(word);
							processed_counter=command_counter;
							response_length=3;										
							break;
						case (unsigned char) SET_BAUD_RATE:
							if (_atmega324p_a2dConvert10bit(ADC4)<350)
								break;
							else if (eeprom_is_ready())
							{
								word=m_BAUD_RATE_BYTE2_TO_BR(aBuffer[1]);
								eeprom_write_word((uint16_t *)BAUD_RATE_ADDRESS,word);
								processed_counter=command_counter;
							}
							break;
						case (unsigned char) GET_BAUD_RATE:
							word=eeprom_read_word((uint16_t *)((uint16_t)BAUD_RATE_ADDRESS));
							aBuffer[0]=m_BAUD_RATE_BYTE0;
							aBuffer[1]=m_BAUD_RATE_BYTE1(word);				
							processed_counter=command_counter;
							response_length=2;										
							break;
						case (unsigned char) SET_CALIBRATION_VALUES:									
							if (eeprom_is_ready())
							{
								//do nothing if battery is low
								if (_atmega324p_a2dConvert10bit(ADC4)<350)
									break;
								else
								{	switch(address)
									{
										case X1G_ADDRESS:
											word=m_CALIBRATION_BYTE2_TO_XN1G(aBuffer[2]) | m_CALIBRATION_BYTE3_TO_XN1G(aBuffer[3]);
											address=X1NG_ADDRESS;
											break;
										case X1NG_ADDRESS:
											word=m_CALIBRATION_BYTE3_TO_Y1G(aBuffer[3])|m_CALIBRATION_BYTE4_TO_Y1G(aBuffer[4])|m_CALIBRATION_BYTE5_TO_Y1G(aBuffer[5]);
											address=Y1G_ADDRESS;
											break;
										case Y1G_ADDRESS:
											word=m_CALIBRATION_BYTE5_TO_YN1G(aBuffer[5])|m_CALIBRATION_BYTE6_TO_YN1G(aBuffer[6]);//(((unsigned short)(aBuffer[5]&0x1f))<<5) | (((unsigned short)(aBuffer[6]&0x7c))>>2);
											address=Y1NG_ADDRESS;
											break;
										case Y1NG_ADDRESS:
											word= m_CALIBRATION_BYTE6_TO_Z1G(aBuffer[6]) | m_CALIBRATION_BYTE7_TO_Z1G(aBuffer[7]) | m_CALIBRATION_BYTE8_TO_Z1G(aBuffer[8]) ;//(((unsigned short)(aBuffer[6]&0x03))<<8) | (((unsigned short)(aBuffer[7]&0x7f))<<1) | (((unsigned short)(aBuffer[8]&0x40))>>6);
											address=Z1G_ADDRESS;
											break;
										case Z1G_ADDRESS:
											word= m_CALIBRATION_BYTE8_TO_ZN1G(aBuffer[8]) |m_CALIBRATION_BYTE9_TO_ZN1G(aBuffer[9]);
											address=Z1NG_ADDRESS;
											processed_counter=command_counter;
											break;
										default:
											word=m_CALIBRATION_BYTE1_TO_X1G(aBuffer[1])| m_CALIBRATION_BYTE2_TO_X1G(aBuffer[2]);																		
											address=X1G_ADDRESS;
											break;																						
									}
									eeprom_write_word((uint16_t *)address,word);
								} 																															
																				
							}															
							//enable global interrupts
							break;
						case (unsigned char) GET_CALIBRATION_VALUES:	
												
							if (eeprom_is_ready())
							{								
								//do nothing if battery is low
								if (_atmega324p_a2dConvert10bit(ADC4)<350)
									break;
								else								
								{
									switch(address)
									{
										case X1G_ADDRESS:
											aBuffer[1]= m_CALIBRATION_X1G_TO_BYTE1(word);									
											aBuffer[2]= m_CALIBRATION_X1G_TO_BYTE2(word);
											address=X1NG_ADDRESS;
											break;
										case X1NG_ADDRESS:
											aBuffer[2]|= m_CALIBRATION_XN1G_TO_BYTE2(word);
											aBuffer[3] =m_CALIBRATION_XN1G_TO_BYTE3(word);
											address=Y1G_ADDRESS;
											break;
										case Y1G_ADDRESS:
											aBuffer[3]|= m_CALIBRATION_Y1G_TO_BYTE3(word);
											aBuffer[4] = m_CALIBRATION_Y1G_TO_BYTE4(word);
											aBuffer[5] =  m_CALIBRATION_Y1G_TO_BYTE5(word);
											address=Y1NG_ADDRESS;
											break;
										case Y1NG_ADDRESS:
											aBuffer[5]|= m_CALIBRATION_YN1G_TO_BYTE5(word);
											aBuffer[6] = m_CALIBRATION_YN1G_TO_BYTE6(word);
											address=Z1G_ADDRESS;
											break;
										case Z1G_ADDRESS:
											aBuffer[6] |= m_CALIBRATION_Z1G_TO_BYTE6(word);
											aBuffer[7] = m_CALIBRATION_Z1G_TO_BYTE7(word);
											aBuffer[8] = m_CALIBRATION_Z1G_TO_BYTE8(word);
											address=Z1NG_ADDRESS;
											break;
										case Z1NG_ADDRESS:
											aBuffer[8] |= m_CALIBRATION_ZN1G_TO_BYTE8(word);
											aBuffer[9] = m_CALIBRATION_ZN1G_TO_BYTE9(word);
											processed_counter=command_counter;
											response_length=10;
											break;
										default:
											aBuffer[0]=m_CALIBRATION_BYTE0;	
											address=X1G_ADDRESS;
											break;																						
									}
									word=eeprom_read_word((uint16_t *)((uint16_t)address));
								} 																						
							
							}							
							break;					
						default:	
							break;

					}

					if (processed_counter==command_counter){					
							
				
						for (i=0;(i<response_length);i++)											
							TransmitByte(aBuffer[i]);										
												
						command_length=0;
						command_counter=0;
						command_timer=0;
						processed_counter=0;						
						address=0xffff;
						response_length=0;
						
					}
				} //if command timed out
				else if (command_timer>=MAX_COMMAND_TIMER)
				{
							
					command_length=0;
					command_counter=0;
					command_timer=0;
					processed_counter=0;				
					address=0xffff;
					response_length=0;
				}
					
				alive_timer++;					
				if (alive_timer>=2730) //if no acks for approx 30 seconds, reset radio
				{
					_atmega324p_reset();
					alive_timer=0;					
				}
					 					
				adc_result[ADC1]=_atmega324p_a2dConvert10bit(ADC1);
				adc_result[ADC2]=_atmega324p_a2dConvert10bit(ADC2);
				adc_result[ADC3]=_atmega324p_a2dConvert10bit(ADC3);
				
				//tag if close to ack
				if (ack==0xff)
				TransmitFrame(encode(1,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));
					//TransmitFrame(encode(1,sequence & 0xff,(sequence>>8)&0xff,0));//adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));
				else  //otherwise dont tag
				TransmitFrame(encode(0,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));
					//TransmitFrame(encode(0,sequence & 0xff,(sequence>>8)&0xff,0));///adc_result[ADC3], adc_result[ADC2], adc_result[ADC1]));

				sequence++;

			}else{  //not connected

				//reset the radio once
				if (disconnected_reset==0){
					_atmega324p_reset();
					disconnected_reset=1;
				}

				sleep_counter++;

				if (sleep_counter>=91)
				{
					sleep_counter=0;
					sleep_counter2++;
				}
				
				//sleep after 1 hour
				if (sleep_counter2>3600)				
					sleep=1;					
			}
				
		}

}

