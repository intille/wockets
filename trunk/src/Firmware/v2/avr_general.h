//*****************************************************************************
//
// File Name    : 'avr_general.h'
// Title        : AVR general functions
// Author       : Fahd Albinali and Ranbel Sun
// Created      : 12/10/2008
// 
//  Description : This include general functions that are used with AVR microcontrollers
//                  
//
// This code is distributed under the MIT License
//     
//
//*****************************************************************************
 

//max and min values held by unsigned and signed variables
#define MAX_U08 255
#define MAX_U16 65535
#define MAX_U32 4294967295
#define MIN_S08 -128
#define MAX_S08 127
#define MIN_S16 -32768
#define MAX_S16 32767
#define MIN_S32 -2147483648
#define MAX_S32 2147483647

#define 	set(addr, data)   addr = (data)
#define 	get(addr)   (addr)
#define cbi(reg,bit)    reg &= ~(BV(bit)) // Macro that clears a bit
#define sbi(reg,bit)    reg |= (BV(bit)) // Macro that sets a bit


/*** AVR Macors ***/
#define BV(bit)         (1<<(bit)) //Macro that shifts a 1 to  a particular bit





