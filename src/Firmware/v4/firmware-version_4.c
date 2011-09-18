//*****************************************************************************
//
// File Name    : 'firmware-version_4.c'
// Title        : Interrupt driven code for the wockets
// Author       : Fahd Albinali
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



data_unit data[750];					// Structure defined in wocket.h has 16 unsigned char bytes per data_unit
unsigned short acount[AC_BUFFER_SIZE]; //array 960 capacity => If 1 AC (activity count) per minute = 16h of capacity 
// acount buffer is used to store activity counts in case the wocket's losses the Blutooth connection (phone)
unsigned short AC_NUMS=0;
unsigned short AC_SCALING=24; // Scaling factor is based on previous testing and explained below 
/* 2 bytes or 16 bit activity count is sent to the phone every minute [an integration of 2400 samples of filtered
raw data (using a moving average filter) where 2400 is 60x40samples]. 16 bit activity count was chosen due to memory
limitations on the mcu [required to store 1.5 minutes of raw data and 16 hours of activity counts]
The integration for activity counts will cause the 16 bit number to overflow, based on experimentation with a 
4g accelerometer with a 10-bit ADC, 24 was determined to be a reasonable scaling factor that allows for the 
capture of high intensity activity without overflow */

/*Quick calculation: Summary Data or activity counts = 16bits = 2bytes X 960 (16hrs x60) = 1920 bytes; 
Raw Data= 30 bits X 40 samples = 1200 bits = 150 bytes /second which leads to 9000 bytes/minute 
Storage of raw data for 1.5 minutes equals 13500  bytes

Total = 1920 +13500= 15420/1024 ~ 15Kbyes
The MCU has 16K memory and at least 1K of memory is used for locals */


unsigned short summaryindex=0;
unsigned short summary_count=2400;  //One minute worth of activity counts


/* Cseq, ci, si, sseq: A circular buffer for the activity counts of size 960 (60 mins x16 hours) is maintained
on the mcu locally. 
ci is a pointer that points to the next empty slot. 
si points to the oldest value in the buffer (i.e. the next value to be sent out or was sent out but no acknowledgment
received from the phone). 
The wockets firmware will send activity count data starting from the data pointed by si.
Cseq and sseq hold the sequence numbers of the entries in ci and si, respectively. The sequence numbers always grow 
and sseq<=cseq.  
In some older hardware versions, the wockets used to reset easily, which caused the seq #s to reset and therefore 
the receiver would get out of sync seeing small seq numbers that were already ACKed. 
In the code, there is a test done to deal with that situation. */
unsigned short cseq=0;
unsigned short sseq=0;
unsigned short kseq=0;
unsigned short dseq=0;
unsigned short ci=0;
unsigned short si=0;


unsigned char gotack=0;				// When the wocket receives an ACK form the Phone


unsigned short x;					// Acceleration values of x, y and z axis
unsigned short y;
unsigned short z;

unsigned short battery; 			// Contains battery level after sampling the battery 

unsigned short prevx;				// Previous acceleration values x 
unsigned short prevy;				// Previous acceleration values y
unsigned short prevz;				// Previous acceleration values z 
unsigned char deltasign;			/* is a variable that has the information if acc is < 32 in any or all axes;
 Is set to zero or one based on increment and decrement compared to the previous*/
unsigned char compress=0;			/* Flag that decides if the data that is to be sent is compressed or not; 
Initialized int the firmware to send at least first batch of bytes or data */

unsigned short dataIndex;			// Used for data buffer; Limit is 750 
unsigned char dataSubindex;			// Used for sub data buffer and has a max value of 4
unsigned char sampleFlag=0;			// Flag to sample the ADC; gets set by the timer ISR	
unsigned short batch_counter=0;		/* Number of bytes that need to be sent to the phone; Raw and activity
 count data is sent in the burst mode */

/* Interrupt Service Routines */
unsigned int seconds_passed=0;		// Counter to keep sampling accelerometer
unsigned int seconds_passed2=0;		// Currently Not used
unsigned int counter=0;				// Currently Not used

unsigned char skip_interrupt_counter=0;		// Currently Not used
unsigned char connected=0;				// To indicate if the wocket is connected to the phone
unsigned int seconds_disconnected=0;	// To incur delay in the Timer ISR

unsigned short configurationTimer=1;	// Currently Not used
unsigned char interrupts_passed=0;

unsigned char interrupt_reps=0;		/* Used to skip sampling depending on the sampling rate variables/timers
 in the timer ISR */
unsigned short docking_counter=0;		// Currently Not used


/* Butterworth Filter */
//double b[5]= {0.0051,0.0,-0.0103,0.0,0.0051};
//double a[5]= { 1.00, -3.7856, 5.3793, -3.4016, 0.8079};
unsigned short xv[3][40];		// The vector of acceleration values for one second xv[3][40];
//double yv[3][5];
unsigned long vmag;				// Sum of the filter from 3 axis
double vmags;					// Currently Not used
unsigned short val;				// Currently Not used
unsigned char justconnected=0;	// Flag to identify when the wocket got connected
unsigned short blink_counter;	/*// Is used in the timer2 ISR to blink green LED when connected or not
 connected  Green will blink in either continuous (when not connected) or burt modes */
unsigned char isdocked=0;		// Flag to indicate while charging or programming
unsigned int dockcounter=0;		/* Counter to prevent resetting the wocket, which would lead to losing of the 
activity count data, if someone might plug in the wocket for a short time accidentally. The counter is used to
 count up to 2400 and then shutdown the radio and reset variables to allow for faster charging.*/

unsigned int pseq=0;			// Currently Not used
unsigned int cc=0;				// Currently Not used

/* Function to filter data used for the activity count */
unsigned short Filter(unsigned short data,int axis)
{
	 unsigned short mean=0;
     int j=0;           
     for (; (j < _SAMPLING_RATE); j++)	// sampling rate (j < 40)
	 {
	 	  mean+=xv[axis][j];
          xv[axis][j] = xv[axis][j + 1];		  		  
	 }
	 mean=mean/_SAMPLING_RATE;
     xv[axis][j] = data;
         
				 
	 if (data>mean)
	 	return (data-mean);
	 else
	 	return (mean-data);      
}

/*Function to perform differential compression, looks like the compression is performed 
whenever the difference of the acceleration values on all three axes is lower than 32 */

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




/* Main function */
int main()
{

   /* This sections checks if the wocket is docked if so it waits in a loop for 10seconds*/

	if (_is_docked())
	{

		for(int j=0;(j<10);j++)			// 10 seconds wait
			for(int i=0;(i<200);i++)
				_delay_ms(5);
	}
				
	scounter=0;							// NOT BEING USED

	//Initialized data buffer
	dataIndex=0;						// Data number for 1 minute: 40*60 = 2400
	dataSubindex=0;

	// Blink green for 5 seconds	
	_wocket_initialize();
		

	AC_NUMS=_SAMPLING_RATE *60;

	/*Functions used for optimizing power by shutting down different peripherals. 
	These functions are part of the external dependencies provided by AVR software power.h*/
	power_adc_disable();
  	power_spi_disable();
  	power_timer0_disable();
  	power_timer1_disable();
  	power_twi_disable();


	/*Loop indefinitely*/
	while(1)
	{
			

		//Sample only in the main loop because of p, low power mode
		if(sampleFlag)		// Sample flag is turned ON in the timer 2 ISR (OVR)
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
					vmag=vmag/AC_SCALING;	/* Scaling has been discussed during the
					 declaration of the variable in the file firmware-version_4.c above */
					
					if (vmag>65535)
						acount[ci]=65535;	// Ceiling of the activity counts	
					else
						acount[ci]=(unsigned short) vmag; /* probably the activity counts 
						is the sum of the magnitude of the three axes */

				 		vmag=0;
						++ci;

						if (ci==AC_BUFFER_SIZE)
							ci=0;
						cseq++;		/* if the activity counts for the first 16 hours are 
						full then increment the c sequence	*/	
		
						if (ci==si)
						{
							si++;
							if (si==AC_BUFFER_SIZE)
								si=0;
							sseq++;
						}
						acount[ci]=0;
						summary_count=AC_NUMS;	/* 1 minute Summary counter Sampling rate*60 
						here 2400, is associated with activity counts */
				}
				else
						summary_count--;
			}
			else if (_wPC==40)		// discard the first 40 samples for the vmag
		  	{			
				vmag=0;
			}


			//This was used in the old version of the code (version 2 with micro-usb)
			//--// #else 
				//x=_atmega_a2dConvert10bit(ADC3);
				//y=_atmega_a2dConvert10bit(ADC2);
				//z=_atmega_a2dConvert10bit(ADC1);		
			//--// #endif
		

			//Save the raw data in an optimized manner to the RAM
			// This section of code stores the data on the RAM in an optimized manner in wocket.h 
			 m_SET_X(data[dataIndex],x,dataSubindex);
			 m_SET_Y(data[dataIndex],y,dataSubindex);
			 m_SET_Z(data[dataIndex],z,dataSubindex);

			 dataSubindex++;

			 if (dataSubindex>=4)	// because there are 16 bytes of information
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

				/* based on this it looks like if the firmware is in continous mode then it will 
				not compress the data */
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
				// Probably used to identify the data that needs to be sent via wireless connection 
				// BATCH_Counter < 1minute raw and activity count data 
				                
				if ((dataSubindex==0) && (batch_counter<750))
					batch_counter++;

				// Increment the second data that needs to be sent 
				if (connected)			// check for the BT connection
				{
					_greenled_turn_on();
						
					gotack=1;
					tester=0;

					if (_wTM==_TM_Continuous) /* Skips sending that particular batch data if the 
					phone requests for a mode change */
						continue;
                   

					
                   //---------------------
				   // Test Code
				    _delay_ms(5);
					_receive_data();
						
					//-------------------
					/* Once the wocket is connected to a phone, it immediately sends data. For some 
					phones (devices) we lose initial packets of the data stream, transmitted by 
					the wockets. The loss of data is probably due to some problem that
					occurs on the receiving end (phone) during the connection setup. The current 
					design of the wockets does not have the capability to allow flow control using 
					RTS/CTS. Instead, we delay the transmission of the actual data (activity counts 
					or raw data) by sending padding bytes. The decoder software on the phone ignores
					the (0xff) bytes received by the phone.*/
					for (int ixz=0;(ixz<100);ixz++) 
					{                                                                                      
       					
						_bluetooth_transmit_uart0_byte(0xff); /* Currently the decode on the phone
						 ignores these packets */

							
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
										vmag=vmag/AC_SCALING;
										if (vmag>65535)
											acount[ci]=65535;	// Ceiling if above the max value
										else
											acount[ci]=(unsigned short) vmag;
			 							vmag=0;
										++ci;
										if (ci==AC_BUFFER_SIZE)
											ci=0;
										cseq++;		/* if the activity counts for the first 16 
										hours are full then increment the c sequence	*/	
	
										if (ci==si)
										{
											si++;
											if (si==AC_BUFFER_SIZE)
												si=0;
											sseq++;
										}
										acount[ci]=0;
										summary_count=AC_NUMS; /* // 1 minute Summary counter 
										Samplingrate*60 = 2400, is associated with activity counts*/
									}else
										summary_count--; // Discard the first 40 samples for the vmag
								}
								else if (_wPC==40)
									vmag=0;
				
								// storing data on the memory 
			 					m_SET_X(data[dataIndex],x,dataSubindex);
			 					m_SET_Y(data[dataIndex],y,dataSubindex);
			 					m_SET_Z(data[dataIndex],z,dataSubindex);

			 					dataSubindex++;
			 					if (dataSubindex>=4)
			 					dataSubindex=0;
							}						
					}

					
				
				// Test Code ----------------
					//_send_fv();
					//_send_hv();					
					_send_sr();			// Send the sampling rate to the phone 				 
					_send_tm();			// Send the transmission mode to the phone
						

					//sample and send the battery level
					battery =_atmega_a2dConvert10bit(ADC7); 
					_send_bl(battery);	// Send the battery level to the phone	
				//----------------------------

					//send activity counts information
					_send_batch_count((batch_counter-1)*4);	/* Send the batch count 
					will send number of activity counts in the batch to the  phone*/																
					_send_acs();		// Send the Activity counts to the phone


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
						// Upto a minute and a half of raw data is sent 
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
										vmag=vmag/AC_SCALING;
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
								}	//End of if (_wPC>40)
								else if (_wPC==40)
									vmag=0;

		
		
			 					m_SET_X(data[dataIndex],x,dataSubindex);
			 					m_SET_Y(data[dataIndex],y,dataSubindex);
			 					m_SET_Z(data[dataIndex],z,dataSubindex);

			 					dataSubindex++;
			 					if (dataSubindex>=4)
			 						dataSubindex=0;
							}	//End of if(sample_flag)
						}		// End of for (int i=0;(i<(batch_counter-1));i++)	

						
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
					else		// Crcular buffer sending last bytes of data
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
										vmag=vmag/AC_SCALING;
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
										vmag=vmag/AC_SCALING;
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
			/// Built in functionality to enable interrupts and shutdown of the cpu to save power 
    		sleep_enable();		// sleep.h 
    		sleep_bod_disable(); 	// sleep.h 
    		sei();		//interrupt.h
    		sleep_cpu();		// sleep.h 
    		sleep_disable();	// sleep.h 	


	}

	return 0;
}



/* Interrupt service routine for Timer 2*/


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
		dockcounter++;		// 2400/40 = 1 minute of docking at least 
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
		if (isdocked)	// Probably isdocked is a FLAG which is reset in this routine
		{
			_bluetooth_turn_on();
			isdocked=0;			
		}
	}

	if (connected==0){
		blink_counter++;
		if (blink_counter==(_SAMPLING_RATE*5))		// ON period: 40*5 =200
			_greenled_turn_on();
		else if (blink_counter==((_SAMPLING_RATE*5)+10)) 	// OFF period: 40*5 +10 =200 +10
		{
			_greenled_turn_off();
			blink_counter=0;
		}

	}



    //Commented -----------------------------------
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
//---------------------------------------------------



	/* Skip sampling depending on the sampling rate variables/timers */
	/*REFER _wocket_initialize_timer2_interrupt as the sampling hass to 
	be much slower than the MCU can actually sample ( 40HZ) */
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
		// Section of the code to indicate that the wocket got connected
		if (!_bluetooth_is_connected())
		{
			justconnected=0;
			compress=0; 
			
			//---Commented -------
			//false
			//if (_wPDT!=0){
			//	_wShutdownTimer--;
				//if (_wShutdownTimer==0)
				//	_atmega_finalize();
			//}
			//---------------------

			return;		
		}
		else if (justconnected==0)
			justconnected=1;


		if (_wShutdownTimer!=_DEFAULT_SHUTDOWN)
			_wShutdownTimer=_DEFAULT_SHUTDOWN;


		_receive_data();

	}
	else if (_wTM==_TM_Burst_60)
	{

		//This only works for Timer1,doesn't have any effect for this timer (Timer2)
		if (_wPDT!=0)
			_wShutdownTimer--;


		//Increase the packet counter
		 _wPC++;
/* Segment of the code that turns the Bluetooth ON every 45 seconds approximately 
after a previous transmission to have the wocket ready for a connection. */

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



