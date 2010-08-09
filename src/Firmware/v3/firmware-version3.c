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


/*data_unit data1[100];
data_unit data2[100];
data_unit data3[100];
data_unit data4[100];
data_unit data5[100];
data_unit data6[100];
data_unit data7[50];*/

//unsigned short xs[3000];
//unsigned short ys[3000];
//unsigned short zs[3000];

data_unit data[750];
unsigned short acount[960]; //16 hours
unsigned short summaryindex=0;
unsigned short summary_count=2400;

//data_unit pose[360];

unsigned short x;
unsigned short y;
unsigned short z;
unsigned short prevx;
unsigned short prevy;
unsigned short prevz;
unsigned char deltasign;
unsigned char compress=0;

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
unsigned short docking_counter=0;


/* Butterworth Filter */
//double b[5]= {0.0051,0.0,-0.0103,0.0,0.0051};
//double a[5]= { 1.00, -3.7856, 5.3793, -3.4016, 0.8079};
double xv[3][40];
//double yv[3][5];
double vmag;
unsigned short vmags;
unsigned short val;

double Filter(unsigned short data,int axis)
{
//     double filtered=0;
	 double mean=0;
     int j=0;           
     for (; (j < 39); j++){
          xv[axis][j] = xv[axis][j + 1];
		  mean+=xv[axis][j];
		  }
	mean=mean/39;
      xv[axis][j] = data;

      /*j = 0;
      for (; (j < 4); j++)
	  {
           yv[axis][j] = yv[axis][j + 1];
		   mean+=yv[axis][j];
		}
      yv[axis][j] = 0;
	  mean=mean/4;


      for (int k = 0; (k < 5); k++)
         yv[axis][j] += b[k] * xv[axis][k];
      for (int k = 1; (k < 5); k++)
            yv[axis][j] -= a[k] * yv[axis][4 - k];

      filtered= yv[axis][j];    */	         
      return (data-mean);
}



static __inline__ void _send_pdu(unsigned short x, unsigned short y, unsigned short z){	
	if(compress)
					{
						deltasign=0;
						if (x>prevx)
						{
							deltasign |=0x01;
							prevx=x-prevx;
						}
						else
							prevx=prevx-x;
						if (y>prevy)
						{
							deltasign |=0x02;
							prevy=y-prevy;
						}
						else
							prevy=prevy-y;
						if (z>prevz)
						{
							deltasign |=0x04;
							prevz=z-prevz;
						}
						else
							prevz=prevz-z;
						if ((prevx<32) && (prevy<32) && (prevz<32))
							//_send_uncompressed_pdu(x,y,z);
							//_send_compressed_pdu(30,20,15);
							_send_compressed_pdu((prevx | ((deltasign &0x01)<<5)),(prevy | ((deltasign &0x02)<<4)),(prevz | ((deltasign &0x04)<<3)));
						else
							_send_uncompressed_pdu(x,y,z);
					}
					else
					{
					 	_send_uncompressed_pdu(x,y,z);
						compress=1;
					}
					prevx=x;
					prevy=y;
					prevz=z;

}

int main()
{
				
scounter=0;


	//Initialized data buffer
	dataIndex=0;
	dataSubindex=0;
	// Blink green for 5 seconds	

	_wocket_initialize();
		

	power_adc_disable();
  	power_spi_disable();
  	power_timer0_disable();
  	power_timer1_disable();
  	power_twi_disable();


	while(1){
			

			

		//Sample only in the main loop because of p
		if(sampleFlag){
			power_adc_enable();
			_atmega_adc_turn_on();
#ifdef _VERSION ==3
			x=_atmega_a2dConvert10bit(ADC2);
		
			y=_atmega_a2dConvert10bit(ADC1);

			z=_atmega_a2dConvert10bit(ADC0);
	

		if (_wTM!=_TM_Continuous)
			{

			val=Filter(x,0);			
			vmag=val;
			val= Filter(y,1);			
			vmag+=val;
			val = Filter(z,2);			
			vmag+=val;
			vmags=vmag+acount[summaryindex];
			
			if (vmags>65535.0)
				acount[summaryindex]=65535;
			else
				acount[summaryindex]=(unsigned short)vmags;//+=(unsigned short)vmag;
			

			if (summary_count==0)
			{
				++summaryindex;
				if (summaryindex==960)
					summaryindex=0;
				acount[summaryindex]=0;
				summary_count=2400;
			}else
				summary_count--;
			}
#else
			x=_atmega_a2dConvert10bit(ADC3);
			y=_atmega_a2dConvert10bit(ADC2);
			z=_atmega_a2dConvert10bit(ADC1);		
#endif
		

			 m_SET_X(data[dataIndex],x,dataSubindex);
			 m_SET_Y(data[dataIndex],y,dataSubindex);
			 m_SET_Z(data[dataIndex],z,dataSubindex);

			 dataSubindex++;
			 if (dataSubindex>=4)
			 	dataSubindex=0;
			 
			 //Most of the time the data buffer with 750 will not overflow
			 //and will be enough to transmit the data, data will go from 0 up to a specific
			 //value

			if (_wTM==_TM_Continuous)
			{

				
				switch(dataSubindex){
				case 1:
						m_GET_X(x,data[dataIndex].byte1,data[dataIndex].byte2,0);
						m_GET_Y(y,data[dataIndex].byte2,data[dataIndex].byte3,0);
						m_GET_Z(z,data[dataIndex].byte3,data[dataIndex].byte4,0);
						break;
				case 2:
						m_GET_X(x,data[dataIndex].byte4,data[dataIndex].byte5,1);
						m_GET_Y(y,data[dataIndex].byte6,data[dataIndex].byte7,1);
						m_GET_Z(z,data[dataIndex].byte7,data[dataIndex].byte8,1);
						break;
				case 3:
						m_GET_X(x,data[dataIndex].byte8,data[dataIndex].byte9,2);
						m_GET_Y(y,data[dataIndex].byte9,data[dataIndex].byte10,2);
						m_GET_Z(z,data[dataIndex].byte11,data[dataIndex].byte12,2);
						break;
				case 0:
						m_GET_X(x,data[dataIndex].byte12,data[dataIndex].byte13,3);
						m_GET_Y(y,data[dataIndex].byte13,data[dataIndex].byte14,3);
						m_GET_Z(z,data[dataIndex].byte14,data[dataIndex].byte15,3);
						break;
				}
											
				//_transmit_packet(_encode_packet( x, y, z));	
				//_send_uncompressed_pdu(x, y, z);
				//_send_pdu(x,y,z);
				_send_pdu(x,y,z);

			}
			else 
			{
				if ((dataSubindex==0) && (batch_counter<750))
					batch_counter++;
				if (connected){
					_greenled_turn_on();
					
					_send_sr();
					_send_batch_count(batch_counter*4);


					for (int i=0;(i<summaryindex);i++){
						_send_summary_count(acount[i]);
						acount[i]=0;
					}

					if (summaryindex<960)
						acount[0]=acount[summaryindex];
					summaryindex=0;
					
					if (batch_counter<750) // Go from 0 up to batch_counter
					{						
						for (int i=0;(i<batch_counter);i++)
						{
							m_GET_X(x,data[i].byte1,data[i].byte2,0);
							m_GET_Y(y,data[i].byte2,data[i].byte3,0);
							m_GET_Z(z,data[i].byte3,data[i].byte4,0);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							m_GET_X(x,data[i].byte4,data[i].byte5,1);
							m_GET_Y(y,data[i].byte6,data[i].byte7,1);
							m_GET_Z(z,data[i].byte7,data[i].byte8,1);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							m_GET_X(x,data[i].byte8,data[i].byte9,2);
							m_GET_Y(y,data[i].byte9,data[i].byte10,2);
							m_GET_Z(z,data[i].byte11,data[i].byte12,2);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							m_GET_X(x,data[i].byte12,data[i].byte13,3);
							m_GET_Y(y,data[i].byte13,data[i].byte14,3);
							m_GET_Z(z,data[i].byte14,data[i].byte15,3);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);
						}
					}else{

						int current=dataIndex+1;
						int end =dataIndex;
						if (current>=750)
							current=0;
						while(current!=end)
						{
							m_GET_X(x,data[current].byte1,data[current].byte2,0);
							m_GET_Y(y,data[current].byte2,data[current].byte3,0);
							m_GET_Z(z,data[current].byte3,data[current].byte4,0);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							m_GET_X(x,data[current].byte4,data[current].byte5,1);
							m_GET_Y(y,data[current].byte6,data[current].byte7,1);
							m_GET_Z(z,data[current].byte7,data[current].byte8,1);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							m_GET_X(x,data[current].byte8,data[current].byte9,2);
							m_GET_Y(y,data[current].byte9,data[current].byte10,2);
							m_GET_Z(z,data[current].byte11,data[current].byte12,2);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							m_GET_X(x,data[current].byte12,data[current].byte13,3);
							m_GET_Y(y,data[current].byte13,data[current].byte14,3);
							m_GET_Z(z,data[current].byte14,data[current].byte15,3);
							//_transmit_packet(_encode_packet(x,y,z));
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							current++;
							if (current==750)
								current=0;
						}

						//copy end item into start
						data[0].byte1=data[end].byte1;
						data[0].byte2=data[end].byte2;
						data[0].byte3=data[end].byte3;
						data[0].byte4=data[end].byte4;
						data[0].byte5=data[end].byte5;
						data[0].byte6=data[end].byte6;
						data[0].byte7=data[end].byte7;
						data[0].byte8=data[end].byte8;
						data[0].byte9=data[end].byte9;
						data[0].byte10=data[end].byte10;
						data[0].byte11=data[end].byte11;
						data[0].byte12=data[end].byte12;
						data[0].byte13=data[end].byte13;
						data[0].byte14=data[end].byte14;
						data[0].byte15=data[end].byte15;
					}

					batch_counter=0;
					dataIndex=0;
					seconds_passed=0;
					while (seconds_passed<400)
					{
						_delay_ms(5);
						seconds_passed++;

					}						
					connected=0;
					_bluetooth_turn_off();		
					seconds_disconnected=0;
					_greenled_turn_off();
				
				}
			}
			_atmega_adc_turn_off();
			power_adc_disable();

			if (dataSubindex==0)
			{
				dataIndex++;


			}

			if (dataIndex==750)
				dataIndex=0;
			sampleFlag=0;
		}	
		
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

/*	if (_is_docked())
	{
		docking_counter++;

		if (docking_counter>2)
		{
			_yellowled_turn_on();			
			for (int i=0;(i<200);i++)
				_delay_ms(5);
			//_atmega_finalize();
			docking_counter=0;
		}else{
			
			for (int i=0;(i<1000);i++)
				_delay_ms(5);
		}
			_yellowled_turn_off();
			
	//	}
	}
	else if (docking_counter>0)
		docking_counter=0;

*/		
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
	{
		if (!_bluetooth_is_connected())
		{
			compress=0; //false
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


		_receive_data();
	}
	else if (_wTM==_TM_Burst_60)
	{
		if (_wPDT!=0)
			_wShutdownTimer--;

		 _wPC++;

		if (!_bluetooth_is_connected()){
			
			compress=0; 

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



