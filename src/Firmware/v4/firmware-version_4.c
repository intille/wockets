//*****************************************************************************
//
// File Name    : 'firmware-version_4.c'
// Title        : Interrupt driven code for the wockets
// Author       : Fahd Albinali & Selene Mota
// Created      : 12/10/2008
// Modified     : 06/16/2011
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
unsigned short acount[AC_BUFFER_SIZE]; //array 960 capacity => If 1 AC per minute = 16h of capacity
unsigned short AC_NUMS=0;
unsigned short summaryindex=0;
unsigned short summary_count=2400;

unsigned short cseq=0;
unsigned short sseq=0;
unsigned short kseq=0;
unsigned short dseq=0;
unsigned short ci=0;
unsigned short si=0;
unsigned char gotack=0;


unsigned short x;
unsigned short y;
unsigned short z;

unsigned short battery; 

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
unsigned int seconds_passed2=0;
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
unsigned short xv[3][41];
//double yv[3][5];
unsigned long vmag;
double vmags;
unsigned short val;
unsigned char justconnected=0;
unsigned short blink_counter;
unsigned char isdocked=0;
unsigned int dockcounter=0;
unsigned int pseq=0;
unsigned int cc=0;


unsigned short Filter(unsigned short data,int axis)
{
	 unsigned short mean=0;
     int j=0;           
     for (; (j < 40); j++)
	 {
	 	  mean+=xv[axis][j];
          xv[axis][j] = xv[axis][j + 1];		  		  
	 }
	 mean=mean/40;
     xv[axis][j] = data;
         
				 
	 if (data>mean)
	 	return (data-mean);
	 else
	 	return (mean-data);      
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



	if (_is_docked())
	{

		for(int j=0;(j<10);j++)
			for(int i=0;(i<200);i++)
				_delay_ms(5);
	}
				
	scounter=0;

	//Initialized data buffer
	dataIndex=0;
	dataSubindex=0;

	// Blink green for 5 seconds	
	_wocket_initialize();
		

	AC_NUMS=_SAMPLING_RATE *60;

	power_adc_disable();
  	power_spi_disable();
  	power_timer0_disable();
  	power_timer1_disable();
  	power_twi_disable();



	while(1)
	{
			

		//Sample only in the main loop because of p, low power mode
		if(sampleFlag)
		{		
		    //turn on adc and micro controller on board	
			power_adc_enable();
			_atmega_adc_turn_on();
			
			sampleFlag=0;

			//sample the accelerometer and wocket battery level
            
			//--// #ifdef _VERSION ==3
			
			x=_atmega_a2dConvert10bit(ADC0);
		
			y=_atmega_a2dConvert10bit(ADC1);

			z=_atmega_a2dConvert10bit(ADC2);


			//battery =_atmega_a2dConvert10bit(ADC7); 



			//x=y=z=cc++;
			//if (cc>=1024)
			//	cc=0;


			//filter the raw accelerometer data and compute the vector of magnitude
			vmag += Filter(x,0)+Filter(y,1)+Filter(z,2);
			
			
			//Skip the first samples to make sure the buffer is clean	
			if (_wPC>40)
			{			
						
				if (summary_count==0)
				{
					vmag=vmag/24;
					
					if (vmag>65535)
						acount[ci]=65535;
					else
						acount[ci]=(unsigned short) vmag;

				 		vmag=0;
						++ci;

						if (ci==AC_BUFFER_SIZE)
							ci=0;
						cseq++;
		
						if (ci==si)
						{
							si++;
							if (si==AC_BUFFER_SIZE)
								si=0;
							sseq++;
						}
						acount[ci]=0;
						summary_count=AC_NUMS;
				}
				else
						summary_count--;
			}
			else if (_wPC==40)
		  				vmag=0;


			//This was used in the old version of the code (version 2 with micro-usb)
			//--// #else 
				//x=_atmega_a2dConvert10bit(ADC3);
				//y=_atmega_a2dConvert10bit(ADC2);
				//z=_atmega_a2dConvert10bit(ADC1);		
			//--// #endif
		

			//Save the raw data in an optimized manner to the RAM
			 m_SET_X(data[dataIndex],x,dataSubindex);
			 m_SET_Y(data[dataIndex],y,dataSubindex);
			 m_SET_Z(data[dataIndex],z,dataSubindex);

			 dataSubindex++;

			 if (dataSubindex>=4)
			 	dataSubindex=0;
		

			// Get the packets of data from buffer according to the current transmission mode
			//-- Most of the time the data buffer with 750 will not overflow
			//-- and will be enough to transmit the data, data will go from 0 up to a specific
			//-- value

			if (_wTM==_TM_Continuous)
			{
									
				switch(dataSubindex)
				{
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
											
		
		        // if the wocket was just connected, confirm the transmission mode 
				if (justconnected==1)
				{
					_send_tm();
					justconnected=2;
				}		


				// send all the data without any compression
				_send_uncompressed_pdu(x, y, z);


				//_send_pdu(x,y,z);
				
					//Send summary activity count
				/*	for (int i=0;(i<summaryindex);i++){
						_send_summary_count(acount[i]);
						acount[i]=0;
					}
					if (summaryindex<AC_BUFFER_SIZE){
						acount[0]=acount[summaryindex];
						summaryindex=0;
					}*/

			}
			else  //if set to any of the bursty modes
			{

                // increase the batch count
				if ((dataSubindex==0) && (batch_counter<750))
					batch_counter++;


				if (connected)
				{
					_greenled_turn_on();
						
					gotack=1;
					tester=0;

					if (_wTM==_TM_Continuous)
						continue;
						

					for (int ixz=0;(ixz<100);ixz++) 
					{                                                                                      
       					
						_bluetooth_transmit_uart0_byte(0xff); 

							
						if (sampleFlag)
						{
								sampleFlag=0;

								x=_atmega_a2dConvert10bit(ADC0);
		
								y=_atmega_a2dConvert10bit(ADC1);

								z=_atmega_a2dConvert10bit(ADC2);

								
								vmag+=Filter(x,0)+Filter(y,1)+Filter(z,2);
			

								if (_wPC>40){	//Skip the first samples						
									if (summary_count==0)
									{
										vmag=vmag/24;
										if (vmag>65535)
											acount[ci]=65535;
										else
											acount[ci]=(unsigned short) vmag;
			 							vmag=0;
										++ci;
										if (ci==AC_BUFFER_SIZE)
											ci=0;
										cseq++;
	
										if (ci==si)
										{
											si++;
											if (si==AC_BUFFER_SIZE)
												si=0;
											sseq++;
										}
										acount[ci]=0;
										summary_count=AC_NUMS;
									}else
										summary_count--;
								}
								else if (_wPC==40)
									vmag=0;

			

		
			 					m_SET_X(data[dataIndex],x,dataSubindex);
			 					m_SET_Y(data[dataIndex],y,dataSubindex);
			 					m_SET_Z(data[dataIndex],z,dataSubindex);

			 					dataSubindex++;
			 					if (dataSubindex>=4)
			 					dataSubindex=0;
							}						
					}

					
					//send wocket information
					_send_fv();
					_send_hv();
					_send_sr();					 
					_send_tm();


					//sample and send the battery level
					battery =_atmega_a2dConvert10bit(ADC7); 
					_send_bl(battery);


					//send activity counts information
					_send_batch_count((batch_counter-1)*4);																	
					_send_acs();


					//Send summary activity count
					/*for (int i=0;(i<summaryindex);i++){
						_send_summary_count(acount[i]);
						acount[i]=0;
					}
					if (summaryindex<AC_BUFFER_SIZE){
						acount[0]=acount[summaryindex];
						summaryindex=0;
					}*/

					
					//Send raw data
					if ((batch_counter>0) && (batch_counter<750)) // Go from 0 up to batch_counter
					{						
						for (int i=0;(i<(batch_counter-1));i++)
						{
							m_GET_X(x,data[i].byte1,data[i].byte2,0);
							m_GET_Y(y,data[i].byte2,data[i].byte3,0);
							m_GET_Z(z,data[i].byte3,data[i].byte4,0);							
							//_send_uncompressed_pdu(x, y, z);
							
							_send_pdu(x,y,z);

							m_GET_X(x,data[i].byte4,data[i].byte5,1);
							m_GET_Y(y,data[i].byte6,data[i].byte7,1);
							m_GET_Z(z,data[i].byte7,data[i].byte8,1);							
							//_send_uncompressed_pdu(x,y, z);
							
							_send_pdu(x,y,z);

							m_GET_X(x,data[i].byte8,data[i].byte9,2);
							m_GET_Y(y,data[i].byte9,data[i].byte10,2);
							m_GET_Z(z,data[i].byte11,data[i].byte12,2);
							//_send_uncompressed_pdu(x, y, z);
							
							_send_pdu(x,y,z);

							m_GET_X(x,data[i].byte12,data[i].byte13,3);
							m_GET_Y(y,data[i].byte13,data[i].byte14,3);
							m_GET_Z(z,data[i].byte14,data[i].byte15,3);							
							
							
							//_send_uncompressed_pdu(x, y, z);
							_send_pdu(x,y,z);

							_receive_data();


							if (sampleFlag)
							{
								sampleFlag=0;

								x=_atmega_a2dConvert10bit(ADC0);
		
								y=_atmega_a2dConvert10bit(ADC1);

								z=_atmega_a2dConvert10bit(ADC2);


								vmag+=Filter(x,0)+Filter(y,1)+Filter(z,2);
			

								if (_wPC>40){	//Skip the first samples						
									if (summary_count==0)
									{
										vmag=vmag/24;
										if (vmag>65535)
											acount[ci]=65535;
										else
											acount[ci]=(unsigned short) vmag;
			 							vmag=0;
										++ci;
										if (ci==AC_BUFFER_SIZE)
											ci=0;
										cseq++;
	
										if (ci==si)
										{
											si++;
											if (si==AC_BUFFER_SIZE)
												si=0;
											sseq++;
										}
										acount[ci]=0;
										summary_count=AC_NUMS;
									}else
										summary_count--;
								}
								else if (_wPC==40)
									vmag=0;

		
		
			 					m_SET_X(data[dataIndex],x,dataSubindex);
			 					m_SET_Y(data[dataIndex],y,dataSubindex);
			 					m_SET_Z(data[dataIndex],z,dataSubindex);

			 					dataSubindex++;
			 					if (dataSubindex>=4)
			 						dataSubindex=0;
							}
						}

						
						if (batch_counter>0)
						{
						//copy end item into start
						data[0].byte1=data[batch_counter].byte1;
						data[0].byte2=data[batch_counter].byte2;
						data[0].byte3=data[batch_counter].byte3;
						data[0].byte4=data[batch_counter].byte4;
						data[0].byte5=data[batch_counter].byte5;
						data[0].byte6=data[batch_counter].byte6;
						data[0].byte7=data[batch_counter].byte7;
						data[0].byte8=data[batch_counter].byte8;
						data[0].byte9=data[batch_counter].byte9;
						data[0].byte10=data[batch_counter].byte10;
						data[0].byte11=data[batch_counter].byte11;
						data[0].byte12=data[batch_counter].byte12;
						data[0].byte13=data[batch_counter].byte13;
						data[0].byte14=data[batch_counter].byte14;
						data[0].byte15=data[batch_counter].byte15;
						}


					}
					else
					{

						int current=dataIndex+1;
						int end =dataIndex;


						if (current>=750)
							current=0;


						while(current!=end)
						{
							m_GET_X(x,data[current].byte1,data[current].byte2,0);
							m_GET_Y(y,data[current].byte2,data[current].byte3,0);
							m_GET_Z(z,data[current].byte3,data[current].byte4,0);							
							//_send_uncompressed_pdu(x, y, z);
							
							_send_pdu(x,y,z);

							m_GET_X(x,data[current].byte4,data[current].byte5,1);
							m_GET_Y(y,data[current].byte6,data[current].byte7,1);
							m_GET_Z(z,data[current].byte7,data[current].byte8,1);							
							//_send_uncompressed_pdu(x, y, z);
							
							_send_pdu(x,y,z);

							m_GET_X(x,data[current].byte8,data[current].byte9,2);
							m_GET_Y(y,data[current].byte9,data[current].byte10,2);
							m_GET_Z(z,data[current].byte11,data[current].byte12,2);
							//_send_uncompressed_pdu(x, y, z);
							
							_send_pdu(x,y,z);

							m_GET_X(x,data[current].byte12,data[current].byte13,3);
							m_GET_Y(y,data[current].byte13,data[current].byte14,3);
							m_GET_Z(z,data[current].byte14,data[current].byte15,3);							
							//_send_uncompressed_pdu(x,y, z);
							
							_send_pdu(x,y,z);

							current++;

							if (current==750)
								current=0;

							_receive_data();


							if (sampleFlag)
							{
								sampleFlag=0;

								x=_atmega_a2dConvert10bit(ADC0);
		
								y=_atmega_a2dConvert10bit(ADC1);

								z=_atmega_a2dConvert10bit(ADC2);


								vmag+=Filter(x,0)+Filter(y,1)+Filter(z,2);
			

								if (_wPC>40){	//Skip the first samples						
									if (summary_count==0)
									{
										vmag=vmag/24;
										if (vmag>65535)
											acount[ci]=65535;
										else
											acount[ci]=(unsigned short) vmag;
			 							vmag=0;
										++ci;
										if (ci==AC_BUFFER_SIZE)
											ci=0;
										cseq++;
	
										if (ci==si)
										{
											si++;
											if (si==AC_BUFFER_SIZE)
												si=0;
											sseq++;
										}
										acount[ci]=0;
										summary_count=AC_NUMS;
									}else
										summary_count--;
								}
								else if (_wPC==40)
									vmag=0;

			

		
			 					m_SET_X(data[dataIndex],x,dataSubindex);
			 					m_SET_Y(data[dataIndex],y,dataSubindex);
			 					m_SET_Z(data[dataIndex],z,dataSubindex);

			 					dataSubindex++;

			 					if (dataSubindex>=4)
			 					dataSubindex=0;

							}
							
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
						_receive_data();

						if (sampleFlag)
							{
								sampleFlag=0;

								x=_atmega_a2dConvert10bit(ADC0);
		
								y=_atmega_a2dConvert10bit(ADC1);

								z=_atmega_a2dConvert10bit(ADC2);


								vmag+=Filter(x,0)+Filter(y,1)+Filter(z,2);
			

								if (_wPC>40){	//Skip the first samples						
									if (summary_count==0)
									{
										vmag=vmag/24;
										if (vmag>65535)
											acount[ci]=65535;
										else
											acount[ci]=(unsigned short) vmag;
			 							vmag=0;
										++ci;
										if (ci==AC_BUFFER_SIZE)
											ci=0;
										cseq++;
	
										if (ci==si)
										{
											si++;
											if (si==AC_BUFFER_SIZE)
												si=0;
											sseq++;
										}
										acount[ci]=0;
										summary_count=AC_NUMS;
									}else
										summary_count--;
								}
								else if (_wPC==40)
									vmag=0;

			

		
			 					m_SET_X(data[dataIndex],x,dataSubindex);
			 					m_SET_Y(data[dataIndex],y,dataSubindex);
			 					m_SET_Z(data[dataIndex],z,dataSubindex);

			 					dataSubindex++;
			 					if (dataSubindex>=4)
			 					dataSubindex=0;
							}						
					}						
					//connected=0;

					//Don't turn off the radio if a request to switch mode has been received
					if (_wTM==_TM_Continuous)
						_bluetooth_turn_on();	
					else
						_bluetooth_turn_off();		
					
					command_counter=0;
					seconds_disconnected=0;
					_greenled_turn_off();
				
				}
			}

			_atmega_adc_turn_off();
			power_adc_disable();

			if ((dataSubindex==0) && (!connected))
				dataIndex++;
							
			if (dataIndex==750)
				dataIndex=0;

			connected=0;			
			
		}	
		
		    //Clear interruptions and set the system to sleep mode
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
	/*if (cseq<pseq)
	{
		_yellowled_turn_on();
		while(1)
		;
	}
	pseq=cseq;	
	*/

	if (_is_docked())
	{
		dockcounter++;		
		if ((!isdocked)&& (dockcounter>2400)){	
		
				
			ci=0;
			si=0;
			cseq=0; 
			sseq=0;		
			_bluetooth_turn_off();
			isdocked=1;			
		}
		return;
	}else
	{
		dockcounter=0;
		if (isdocked)
		{
			_bluetooth_turn_on();
			isdocked=0;			
		}
	}

	if (connected==0){
		blink_counter++;
		if (blink_counter==(_SAMPLING_RATE*5))
			_greenled_turn_on();
		else if (blink_counter==((_SAMPLING_RATE*5)+10))
		{
			_greenled_turn_off();
			blink_counter=0;
		}

	}
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

		_wPC++;

		if (!_bluetooth_is_connected())
		{
			justconnected=0;
			compress=0; //false
			//if (_wPDT!=0){
			//	_wShutdownTimer--;
				//if (_wShutdownTimer==0)
				//	_atmega_finalize();
			//}
			return;		
		}else if (justconnected==0)
			justconnected=1;

		if (_wShutdownTimer!=_DEFAULT_SHUTDOWN)
			_wShutdownTimer=_DEFAULT_SHUTDOWN;


		_receive_data();
	}
	else if (_wTM==_TM_Burst_60)
	{

		if (_wPDT!=0)
			_wShutdownTimer--;

		 _wPC++;


		if (!_bluetooth_is_connected())
		{
			
			compress=0; 

			if (seconds_disconnected<1800)
				seconds_disconnected++;
			else if (seconds_disconnected==1800)
			{
				//before turning on the bluetooth make sure you flush the receive buffer
				_receive_uart0_flush();
				_bluetooth_turn_on();		
				seconds_disconnected=1801;			
				_delay_ms(10);
			}

			return;	
		}



		//_atmega_initialize_uart0(ATMEGA_BAUD_38400, TX_RX_UART_MODE);
		//_atmega_initialize_uart1(ATMEGA_BAUD_38400, TX_RX_UART_MODE);
	

		//reset shutdown timer if connected
		if ((_wPDT!=0) && (_wShutdownTimer!=_DEFAULT_SHUTDOWN))
			_wShutdownTimer=_DEFAULT_SHUTDOWN;



		_receive_data();		
		connected=1;
		
	}




}



