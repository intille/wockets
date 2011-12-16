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

//-----------------------------------Variables------------------------------------------------------------------------------

unsigned char wakeup = 0;
unsigned char sample = 0;

/*We have a maximum of 16K on the microcontroller. The storage capacity of depends on the sampling rate and that can vary.
With the sampling rate of 40Hz, the memory is allocated as follows:
- approximately 1K is allocated for summary data over 16 hours... specifically 960 bytes.

- 11K for raw data. 750 data units allows us to store over 1.25 Minute of raw data without overflowing.  
(750 x 4)/(60sec x 40sample) = 1.25 min 

12K and the rest goes for the heap and stack.*/

data_unit      data[DATA_SIZE];	/* This structure is used to store raw data. Each data unit (15bytes) consists of 4 samples. 
								Because the accelerometer is sampled using a 10 bit ADC. So, a sample consists of 30 bits for
								the 3 axes. 30x4= 120 bits i.e. 15 bytes.*/
unsigned short batch_counter = 0;// Counter of raw data in bursty mode

unsigned short acount[AC_BUFFER_SIZE]; /* A buffer  with capacity of 960 bytes for storing activity counts up to 16 hours in
									   case the wocket losses the Blutooth connection (with phone)*/ 
unsigned short AC_NUMS = 0;
unsigned short summary_count;
unsigned short AC_SCALING = 24; /* The scaling factor is used to prevent AC to overflow. Based on experimentation with a 4g 
								accelerometer  with a 10-bit ADC, 24 was determined to be a reasonable scaling factor */
unsigned int AC_CEILING = 65535;
/*  ci, si, cseq and sseq: A circular buffer for the activity counts.  
In some older hardware versions, the wockets used to reset easily, which caused the sseq to reset and therefore 
the receiver would get out of sync seeing small seq numbers that were already ACKed. 
In the code, there is a test done to deal with that situation. */

unsigned short cseq = 0;		// the sequence numbers of the last AC
unsigned short sseq = 0;		// the next sequence number that need to be sent to phone
unsigned short kseq = 0;		// the acknowledged sequence number 
unsigned short dseq = 0;		// the difference between the last AC and the new Acknowledged seq: cseq - kseq
unsigned short ci   = 0;		// the pointer in the circular buffer to the last AC. It corresponds to cseq
unsigned short si   = 0;		// the pointer in the circular buffer to the next element to be sent, it corresponds to sseq(i.e. the next value to be sent
								// out or was sent out but no acknowledgment received from the phone). 

unsigned char  gotack = 0;		// When the wocket receives an ACK form the Phone

unsigned short battery; 		// Contains battery level after sampling the battery 

unsigned short x;				// Acceleration values of x, y and z axis
unsigned short y;
unsigned short z;
unsigned int i = 0;

unsigned short prevx;			// Previous acceleration values 
unsigned short prevy;				
unsigned short prevz;	

unsigned short diffx;			// difference of the current and previous acceleration values 
unsigned short diffy;				
unsigned short diffz;

unsigned char  deltasign;		/* Different bits of this variable is set to 1 or 0 to show the positive or negative sign 
								(respectively) of the difference of current and previous accelerometer values for each axis.*/
unsigned char  compress=0;		/* Flag that decides if the data that is to be sent is compressed or not;Initialized int 
								the firmware to send at least first batch of bytes or data */
unsigned short dataIndex;		// Used for data buffer; Limit is DATA_SIZE 
unsigned char  dataSubindex;	// Used for sub data buffer and has a max value of 4
unsigned char  sampleFlag=0;	// Flag to sample the ADC; gets set by the timer ISR	
unsigned int   seconds_passed=0;// Counter to keep sampling accelerometer
unsigned char  connected=0;		// To indicate if the wocket is connected to the phone
unsigned int   seconds_disconnected=0;// To incur delay in the Timer ISR
unsigned char  interrupts_passed=0;
unsigned char  interrupt_reps=0;// Used to skip sampling depending on the sampling rate variables/timers in the timer ISR 
unsigned short xv[3][MAX_SR];   // The vector of acceleration values for one second 
unsigned long  vmag;			// Sum of the filtered value from 3 axis
unsigned char  justconnected=0;	// Flag to identify when the wocket got connected
unsigned short blink_counter;	/* Is used in the timer2 ISR. The wockets blink green once every 5 seconds when they are in 
								either the continuous or bursty mode. blink_counter is a simple counter that is used to 
								implement this */

unsigned char  isdocked=0;		// Flag to indicate while wocket is  connected to charger or programmer
unsigned int   dockcounter=0;	/* Counter to prevent resetting the wocket, if someone plug in the wocket for a short time 
								accidentally. This would lead to loose of the activity count data. The counter is used to 
								count up to 2400 and then shutdown the radio and reset variables to allow for faster charging.*/

//------------------------------------------------------Functions-----------------------------------------------------------------

/* This function sends the raw data to the phone.
Sending a PDU, in an uncompressed mode, requires 10bits per axis. In typical scenarios, the accelerometer 
on the body is not moving or is moving slightly, it is therefore redundant to send the 10bits. Instead, if 
the difference between consecutive values, the differential data, is less than 32 (2^5), the differential
value is sent in compress mode within 5 bits*/
static __inline__ void _send_pdu(unsigned short x, unsigned short y, unsigned short z){	
	if(compress)
	{
		if (x > prevx)
		{
			deltasign |= 0x01; //The first bit from right: sign of difference value in x axis
			diffx = x - prevx;
		}
		else
			diffx = prevx - x;
		
		if (y > prevy)
		{
			deltasign |= 0x02; //The Second bit from right: sign of difference value in y axis
			diffy = y - prevy;
		}
		else
			diffy = prevy - y;   
		
		if (z > prevz)
		{
			deltasign |= 0x04; //The first bit from right: sign of difference value in z axis
			diffz = z - prevz;
		}
		else
			diffz = prevz - z;
		
		if ((diffx < 32) && (diffy < 32) && (diffz < 32))			
			_send_compressed_pdu((diffx | ((deltasign &0x01)<<5)), (diffy | ((deltasign &0x02)<<4)), 
			(diffz | ((deltasign &0x04)<<3)));
		else
			_send_uncompressed_pdu(x, y, z);
	}
	else
	{
	 	_send_uncompressed_pdu(x, y, z);
		compress = 1;
	}
	prevx = x;
	prevy = y;
	prevz = z;
}
//-------------------------------------------

// Averaging the accelerometer values of each axis in one miniute for producing the activity count 
unsigned short Filter(unsigned short data,int axis)
{
	 unsigned short mean = 0;

	 int j=0;                
     for (; (j < _SAMPLING_RATE); j++)	
	 {
	 	  mean += xv[axis][j];	//Initializing the xv is not required because, the activity count is 
		  						//calculated and saved only once per minute when xv is filled with 
								//valid accelerometer data
          xv[axis][j] = xv[axis][j + 1];		  		  
	 }
	 mean = mean / _SAMPLING_RATE;
     xv[axis][j] = data;
     				 
	 if (data > mean)
	 	return (data - mean);
	 else
	 	return (mean - data);      
}

//-------------------------------------------
/* Sampling the accelerometer 
Sampling procedure is done in various parts of the code to ensure that the interups are 
acknowledeged close enough to their occurances*/
void do_sampling()
{
	sampleFlag = 0;
    
	//sample the accelerometer
	x = _atmega_a2dConvert10bit(ADC0);		
	y = _atmega_a2dConvert10bit(ADC1);
	z = _atmega_a2dConvert10bit(ADC2);
	/*if (i==6000) i=0;
	x=y=z=i;
	i++;*/

	//Filter the raw accelerometer data and compute the vector of magnitude (Activity count)
	vmag += Filter(x, 0) + Filter(y, 1) + Filter(z, 2);
		
	//for calculating the activity count, skip the first samples to make sure the buffer is clean	
	if (_wPC > _SAMPLING_RATE)
	{							
		if (summary_count == 0)			// calculate the activity count only once per miniute
		{
			vmag = vmag / AC_SCALING;	// vmag is scaled in order to prevent the overflow 
			
			if (vmag > AC_CEILING)
				acount[ci] = AC_CEILING;// the maximum possible value of activity counts (size: two bytes)	
			else
				acount[ci] = (unsigned short) vmag; 
	 		
			vmag = 0;
			++ci;

			if (ci == AC_BUFFER_SIZE)
				ci = 0;
			cseq++;	// if the activity counts for the first 16 hours are full then increment the c sequence	
			 
			if (ci == si)
			{
				si++;
				if (si == AC_BUFFER_SIZE)
					si = 0;
				sseq++;
			}
			acount[ci] = 0;
			summary_count = AC_NUMS;	// 1 minute Summary counter is associated with activity counts 
		}
		else
			summary_count--;
	}
	else if (_wPC == 40)				// discard the first 40 samples for the vmag  				
		vmag = 0;

	//Save the raw data in the RAM 
	m_SET_X(data[dataIndex], x, dataSubindex);
	m_SET_Y(data[dataIndex], y, dataSubindex);
	m_SET_Z(data[dataIndex], z, dataSubindex);

	dataSubindex++;
	if (dataSubindex >= 4)	
	 	dataSubindex = 0;
}	

//-------------------------------------------
void copy_end_item_to_start(int cnt)
{
	data[0].byte1  = data[cnt].byte1;
	data[0].byte2  = data[cnt].byte2;
	data[0].byte3  = data[cnt].byte3;
	data[0].byte4  = data[cnt].byte4;
	data[0].byte5  = data[cnt].byte5;
	data[0].byte6  = data[cnt].byte6;
	data[0].byte7  = data[cnt].byte7;
	data[0].byte8  = data[cnt].byte8;
	data[0].byte9  = data[cnt].byte9;
	data[0].byte10 = data[cnt].byte10;
	data[0].byte11 = data[cnt].byte11;
	data[0].byte12 = data[cnt].byte12;
	data[0].byte13 = data[cnt].byte13;
	data[0].byte14 = data[cnt].byte14;
	data[0].byte15 = data[cnt].byte15;
}


//----------------------------------- Main function ----------------------------------------------
int main()
{
   // If the wocket is docked, waits for 10 seconds
	if (_is_docked())
	{
		for(int j = 0;(j < 10);j++)			
			for(int i = 0;(i < 200);i++)
				_delay_ms(5);
	}

	//Initialized data buffer
	dataIndex = 0;						// Data number for 1 minute: _SAMPLING_RATE*60
	dataSubindex = 0;

	// Blink green for 5 seconds	
	_wocket_initialize();

	summary_count = _SAMPLING_RATE * 60;
	AC_NUMS = _SAMPLING_RATE * 60;

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
			
			do_sampling(); // To prevent data loss, sampling is done in the "main loop" instead of the 
			               //"Interrupt Service Routine"			
			
			//Get the packets of data from buffer according to the current transmission mode.
			if (_wTM == _WTM_Continuous) //Countinuous Mode
			{		
				switch(dataSubindex)
				{
					case 1:
							m_GET_X(x, data[dataIndex].byte1,  data[dataIndex].byte2,  0);
							m_GET_Y(y, data[dataIndex].byte2,  data[dataIndex].byte3,  0);
							m_GET_Z(z, data[dataIndex].byte3,  data[dataIndex].byte4,  0);
							break;
					case 2:
							m_GET_X(x, data[dataIndex].byte4,  data[dataIndex].byte5,  1);
							m_GET_Y(y, data[dataIndex].byte6,  data[dataIndex].byte7,  1);
							m_GET_Z(z, data[dataIndex].byte7,  data[dataIndex].byte8,  1);
							break;
					case 3:
							m_GET_X(x, data[dataIndex].byte8,  data[dataIndex].byte9,  2);
							m_GET_Y(y, data[dataIndex].byte9,  data[dataIndex].byte10, 2);
							m_GET_Z(z, data[dataIndex].byte11, data[dataIndex].byte12, 2);
							break;
					case 0:
							m_GET_X(x, data[dataIndex].byte12, data[dataIndex].byte13, 3);
							m_GET_Y(y, data[dataIndex].byte13, data[dataIndex].byte14, 3);
							m_GET_Z(z, data[dataIndex].byte14, data[dataIndex].byte15, 3);
							break;
				}											
		
		        // if the wocket was just connected, confirm the wocket transmission mode 
				if (justconnected == 1)
				{
					_send_wtm();
					justconnected = 2;
				}		

				//if the firmware is in continous mode then it will not compress the data
				_send_uncompressed_pdu(x, y, z);
			}
			
			else  //Bursty modes
			{				
				if ((dataSubindex == 0) && (batch_counter < DATA_SIZE))
					batch_counter++;

				if (connected)			// check for the BT connection
				{
					_greenled_turn_on();
						
					gotack = 1;
					tester = 0;

					if (_wTM == _WTM_Continuous) /* Skips sending that particular batch data if the 
					phone requests for a mode change */
						continue;
                   					
                   //Test Code------------
				    _delay_ms(5);
					_receive_data();						
					//-------------------
					
					/* Once the wocket is connected to a phone, it sends data immediately. In some of 
					the phones (devices) we may lose initial packets of the data stream, transmitted 
					by the wockets. The loss of the data is probably due to some problem that occurs 
					on the receiving end (phone) during the connection setup. The current design of 
					the wockets does not have the capability to allow flow control using RTS/CTS. 
					Instead, we delay the transmission of the actual data (activity counts or raw data) 
					by sending padding bytes. The decoder software on the phone ignores the (0xff) bytes
					received by the phone.*/

					for (int ixz = 0; (ixz < 100); ixz++) 
					{                                                                                
       					_bluetooth_transmit_uart0_byte(0xff); /* Currently the decode on the phone
						 ignores these packets */
							
						if (sampleFlag)
							do_sampling();
					} 					
				
				    // Test Code ----------------										
					_send_sr();			// Send the sampling rate to the phone 				 
					_send_wtm();		// Send the wocket transmission mode to the phone						

					//sample and send the battery level
					battery = _atmega_a2dConvert10bit(ADC7); 
					_send_bl(battery);		
				    //----------------------------

					//send activity counts information																
					_send_acs();		// Send the Activity counts to the phone

					// Send the number of raw data bytes in the wocket
					 
					_send_batch_count((batch_counter-1) * 4);	
					
					//Send raw data
					if ((batch_counter > 0) && (batch_counter < DATA_SIZE)) 
					{						
						/*The last entry in the buffer may be partially filled. So, it is not sent. It goes out with the 
						next batch, hence the last data unit is copied to the start of the buffer. */
						for (int i = 0; (i < (batch_counter - 1)); i++)		
						{
							m_GET_X(x, data[i].byte1,  data[i].byte2,  0);
							m_GET_Y(y, data[i].byte2,  data[i].byte3,  0);
							m_GET_Z(z, data[i].byte3,  data[i].byte4,  0);					
							_send_pdu(x, y, z);

							m_GET_X(x, data[i].byte4,  data[i].byte5,  1);
							m_GET_Y(y, data[i].byte6,  data[i].byte7,  1);
							m_GET_Z(z, data[i].byte7,  data[i].byte8,  1);					
							_send_pdu(x, y, z);

							m_GET_X(x, data[i].byte8,  data[i].byte9,  2);
							m_GET_Y(y, data[i].byte9,  data[i].byte10, 2);
							m_GET_Z(z, data[i].byte11, data[i].byte12, 2);				
							_send_pdu(x, y, z);

							m_GET_X(x, data[i].byte12, data[i].byte13, 3);
							m_GET_Y(y, data[i].byte13, data[i].byte14, 3);
							m_GET_Z(z, data[i].byte14, data[i].byte15, 3);
							_send_pdu(x, y, z);

							_receive_data();

							if (sampleFlag)
								do_sampling();
						}	
						
						copy_end_item_to_start(batch_counter);
					}

					else		// Circular buffer sending recent bytes of data
					{
						int current = dataIndex + 1;
						int end = dataIndex;

						if (current >= DATA_SIZE)
							current = 0;

						while(current != end)
						{
							m_GET_X(x, data[current].byte1,  data[current].byte2,  0);
							m_GET_Y(y, data[current].byte2,  data[current].byte3,  0);
							m_GET_Z(z, data[current].byte3,  data[current].byte4,  0);							
							_send_pdu(x, y, z);

							m_GET_X(x, data[current].byte4,  data[current].byte5,  1);
							m_GET_Y(y, data[current].byte6,  data[current].byte7,  1);
							m_GET_Z(z, data[current].byte7,  data[current].byte8,  1);
							_send_pdu(x, y, z);

							m_GET_X(x, data[current].byte8,  data[current].byte9,  2);
							m_GET_Y(y, data[current].byte9,  data[current].byte10, 2);
							m_GET_Z(z, data[current].byte11, data[current].byte12, 2);
							_send_pdu(x, y, z);

							m_GET_X(x, data[current].byte12, data[current].byte13, 3);
							m_GET_Y(y, data[current].byte13, data[current].byte14, 3);
							m_GET_Z(z, data[current].byte14, data[current].byte15, 3);
							_send_pdu(x, y, z);

							current++;

							if (current == DATA_SIZE)
								current = 0;

							_receive_data();

							if (sampleFlag)
								do_sampling();							
						} 

						copy_end_item_to_start(end);
					}	

					batch_counter = 0;
					dataIndex = 0;
					seconds_passed = 0;

					while (seconds_passed < 400) //The delay provided here helps to not lose the sent data from the phone 
					{
						_delay_ms(5);
						seconds_passed++;
						_receive_data();

						if (sampleFlag)
							do_sampling();
					} 

					//Don't turn off the radio if a request to switch mode has been received
					if (_wTM == _WTM_Continuous)
						_bluetooth_turn_on();	
					else
						_bluetooth_turn_off();		
					
					command_counter = 0;
					seconds_disconnected = 0;
					_greenled_turn_off();

				} // End if (connected)

			} // End else (_wTM==_WTM_Continuous) => _wTM is not continuous 

			_atmega_adc_turn_off();
			power_adc_disable();

			if ((dataSubindex == 0) && (!connected))
				dataIndex++;
							
			if (dataIndex == DATA_SIZE)
				dataIndex = 0;

			connected = 0;			
		}// Endof the First if (sampleFlag)	
		
		   
			cli();				// Clear interruptions and set the system to sleep mode
			set_sleep_mode(SLEEP_MODE_IDLE);
			// set_sleep_mode(SLEEP_MODE_PWR_SAVE);
			// Built in functionality to enable interrupts and shutdown of the cpu to save power 
    		sleep_enable();		// sleep.h 
    		sleep_bod_disable();// sleep.h 
    		sei();				//interrupt.h
    		sleep_cpu();		// sleep.h 
    		sleep_disable();	// sleep.h 	

	} // End While(1)

	return 0;
} // End main


//------------------------ Interrupt service routine for Timer 2------------------------------------
ISR(TIMER2_OVF_vect)
{	
	if (_is_docked())
	{
		dockcounter++;		 
		if ((!isdocked)&& (dockcounter > (_SAMPLING_RATE * 60))){	// it shows that the wocket has been connected to the 
			//charger or the programmer more than one minitue					
			ci   = 0;
			si   = 0;
			cseq = 0; 
			sseq = 0;		
			_bluetooth_turn_off();
			isdocked = 1;			
		}
		return;
	}else
	{
		dockcounter = 0;
		if (isdocked)	
		{
			_bluetooth_turn_on();
			isdocked = 0;			
		}
	}

	if (connected == 0){
		blink_counter++;
		if (blink_counter == (_SAMPLING_RATE * 5))		// ON period
			_greenled_turn_on();
		else if (blink_counter == ((_SAMPLING_RATE * 5) + 10)) 	// OFF period
		{
			_greenled_turn_off();
			blink_counter = 0;
		}
	}

	/* Skip sampling depending on the sampling rate variables/timers */
	/*REFER _wocket_initialize_timer2_interrupt 
	The sampling rate is much slower than the MCU  */
 	if (interrupt_reps == 0)
	{	
		interrupt_reps = _wTCNT2_reps;
		TCNT2 = _wTCNT2;
	}
	else{ //otherwise wait
		if (interrupt_reps == 1)	
			TCNT2 = _wTCNT2_last;	
		else		
			TCNT2 = _wTCNT2;					
		interrupt_reps--;
		return;
	}
	
	/* Sample data and transmit it if necessary */
	sampleFlag = 1;

	if (_wTM == _WTM_Continuous)
	{
		_wPC++;
		// Section of the code to indicate that the wocket got connected
		if (!_bluetooth_is_connected())
		{
			justconnected = 0;
			compress = 0;
			return;		
		}
		else if (justconnected == 0)
			justconnected = 1;

		if (_wShutdownTimer != _DEFAULT_SHUTDOWN)
			_wShutdownTimer  = _DEFAULT_SHUTDOWN;

		_receive_data();
	}

	else if (_wTM == _WTM_Burst_60)
	{
		//This only works for Timer1,doesn't have any effect for this timer (Timer2)
		if (_wPDT != 0)
			_wShutdownTimer--;

		_wPC++;
		
		 /* Segment of the code that turns the Bluetooth ON every 45 seconds approximately 
		after a previous transmission to have the wocket ready for a connection. */
		if (!_bluetooth_is_connected())
		{			
			compress = 0; 

			if (seconds_disconnected < (_SAMPLING_RATE * 45)) // 45 Sec
				seconds_disconnected++;
			else if (seconds_disconnected == (_SAMPLING_RATE * 45))
			{
				//before turning on the bluetooth make sure you flush the receive buffer
				_receive_uart0_flush();
				_bluetooth_turn_on();		
				seconds_disconnected = (_SAMPLING_RATE * 45) + 1;			
				_delay_ms(10);
			}

			return;	
		}

		//reset shutdown timer if connected
		if ((_wPDT != 0) && (_wShutdownTimer != _DEFAULT_SHUTDOWN))
			_wShutdownTimer = _DEFAULT_SHUTDOWN;

		_receive_data();		
		connected = 1;		
	}
}




