#include "avr_general.h"
#include "mcu_atmega324p.h"
#include "acc_mma7260qt.h"
#include "bt_rn41.h"
#include "crc.h"
#include "encoder.h"
#include <util/delay.h>
#include <stdlib.h>
#include <avr/io.h>
#define CHANNELID 15
unsigned short adc_result[4];
char buffer[8];
unsigned char i;
unsigned char r;
unsigned char j;
unsigned char crcval;
unsigned int seq_num;
WOCKETS_UNCOMPRESSED_FRAME f[60];
WOCKETS_UNCOMPRESSED_FRAME ss;

int status=0;//disconnected
int firstConnection=0;

void TransmitFrame(WOCKETS_UNCOMPRESSED_FRAME f){
	
	TransmitByte(f.byte1);
	TransmitByte(f.byte2);
	TransmitByte(f.byte3);
	TransmitByte(f.byte4);
	TransmitByte(f.byte5);
	TransmitByte(f.byte6);
	TransmitByte(f.byte7);
	
}


void TransmitFrames(){
	int i=0;
	for (i=0;i<60;i++){
	TransmitByte(f[i].byte1);
	TransmitByte(f[i].byte2);
	TransmitByte(f[i].byte3);
	TransmitByte(f[i].byte4);
	TransmitByte(f[i].byte5);
	TransmitByte(f[i].byte6);
	TransmitByte(f[i].byte7);
	}
}
int main()
{
	r=0;
	seq_num=0;
	//Set up 16-bit counter:
	TCCR1B |= (1<<CS12);  // Clock=8MHz/256, timer resolution= 32 us
	TCNT1=0;
	//i=0xff;
	//init_crc();
	_atmega324p_init();
   for(;;)  {            /* Forever */
	
	
//if (r>100)
//	TransmitByte('W');
//	else
//		TransmitByte(0);
		//PORTD=0XFF;
      //_delay_ms(5000);
		//PORTD=0;
		//_delay_ms(5000);

if (_rn41_is_discoverable())
	_atmega324p_yellow_led_on();
else 
_atmega324p_yellow_led_off();

if (_rn41_is_connected()){
	status=1;

	//for first connection reset sequence number
	if (firstConnection==0){
		firstConnection=1;
		seq_num=0;
	}
	if (TCNT1>=31250){
		_atmega324p_green_led_on();
		}
	else  _atmega324p_green_led_off();
	}
else{
	_atmega324p_green_led_off();

	//reset sequence number if was connected then became disconnected
	if (status==1)
		seq_num=0;
    status=0;
	}

	
		//sample accelerometer data, encode and transmit	
		adc_result[ADC1]=_atmega324p_a2dConvert10bit(ADC1);
		adc_result[ADC2]=_atmega324p_a2dConvert10bit(ADC2);
		adc_result[ADC3]=_atmega324p_a2dConvert10bit(ADC3);
 		//crcval=crc((unsigned char*) adc_result,6);
		crcval=0;
	//	TransmitByte(0x68);
		//ss=encode(CHANNELID,adc_result[ADC0], (seq_num>>8), (seq_num & 0xFF), crcval);
		//f[r].byte1=ss.byte1;
		//f[r].byte2=ss.byte2;
		//f[r].byte3=ss.byte3;
		//f[r].byte4=ss.byte4;
		//f[r].byte5=ss.byte5;
		//f[r].byte6=ss.byte6;
		//f[r].byte7=ss.byte7;
		//r++;
	//if (r==60){
		TransmitFrame(encode(CHANNELID,adc_result[ADC0], (seq_num>>8), (seq_num & 0xFF), crcval));
		//TransmitFrames();
		//r=0;
		//}
	//TransmitFrame(encode(CHANNELID,adc_result[ADC3], adc_result[ADC2], adc_result[ADC1], crcval));

//TransmitByte(0xFF);
//	TransmitByte(0x68);
		
	//r='X';
	//TransmitByte(r);
	//r='W';
	//TransmitByte(r);

		//for debugging
/*		for(i=0;(i<4);i++)
		 		buffer[i]=0;
		 	itoa(crcval,buffer,10);
		 	for(i=0;(i<4);i++)		 	
		 		TransmitByte(buffer[i]);	

		TransmitByte('<');
		for (j=0;(j<3);j++){
			for(i=0;(i<4);i++)
		 		buffer[i]=0;
		 	itoa(adc_result[j],buffer,10);
		 	for(i=0;(i<4);i++)		 	
		 		TransmitByte(buffer[i]);			

			if (j!=2)
				TransmitByte(',');
		}
		TransmitByte('>');*/
		//end debugging
         
		seq_num=seq_num+1;

   		_delay_ms(10);
	}
	return 0;
}
