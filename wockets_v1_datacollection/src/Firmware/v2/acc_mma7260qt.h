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

/*** Sensitivity Levels ***/
#define _1_5G 0
#define _2G 1
#define _4G 2
#define _6G 3

/*** Defining accelerometer PINS ***/

/*** PORTB PINs for accelerometer settings ***/

#define ACC_CONTROL_PORT PORTB
#define GS1_PIN 0
#define GS2_PIN 1
#define SLP_PIN 3

/*** PORTA PINs for ADC ***/
#define ACC_DATA_PORT PORTA
#define X_PIN 3
#define Y_PIN 2
#define Z_PIN 1

//move the following control pins to separate file later
#define VSENSE_COMP_PB 2 //set as input
#define VSENSE_COMP_PA 0 //set as input
#define VSENSE_BAT 4 //set as input
#define DOCK_N 5 //set as input



unsigned char sensitivity;

void _mma7260qt_init();
unsigned char _mma7260qt_set_sensitivity(unsigned char level);
void _mma7260qt_wakeup();
void _mma7260qt_sleep();
unsigned char _mma7260qt_is_asleep();
