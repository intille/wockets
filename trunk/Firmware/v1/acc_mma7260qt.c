#include <avr/io.h>
#include "avr_general.h"
#include "acc_mma7260qt.h"


/** Here we will set the direction of the different ports ***/

int _mma7260qt_set_sensitivity(unsigned char level){
  	
	if (level==_1_5G){
		cbi(PORTB,GS1_PIN);
		cbi(PORTB,GS2_PIN);
		return 1;
	}else if (level==_2G){
		sbi(PORTB,GS1_PIN);
		cbi(PORTB,GS2_PIN);
		return 1;
	}else if (level==_4G){
		sbi(PORTB,GS2_PIN);
		cbi(PORTB,GS1_PIN);
		return 1;
	}else if (level==_6G){
		sbi(PORTB,GS1_PIN);
		sbi(PORTB,GS2_PIN);
		return 1;
	}

	return 0;
}

void _mma7260qt_wakeup(){
	sbi(PORTB,SLP_PIN);

}

void _mma7260qt_sleep(){
	cbi(PORTB,SLP_PIN);
}

unsigned char _mma7260qt_is_asleep(){

	return (0x01 & ~(PORTB>>SLP_PIN));
}

//by default set sensitivity to 1.5G
void _mma7260qt_init(){
	
	sbi(DDRB,GS1_PIN); //set to output
	sbi(DDRB,GS2_PIN); //set to output
	sbi(DDRB,SLP_PIN); //set to output

	//set X,Y,Z pins to input
	cbi(DDRA, X_PIN);
	cbi(DDRA, Y_PIN);
	cbi(DDRA, Z_PIN);

	//set other control pins to inputs --> move to seperate file later
	cbi(DDRB, VSENSE_COMP_PB);
	cbi(DDRA, VSENSE_COMP_PA);
	cbi(DDRA, VSENSE_BAT);
	cbi(DDRA, DOCK_N);

	//set default sensitivity to 1.5G
	_mma7260qt_set_sensitivity(_1_5G);
	//_mma7260qt_sleep(); //initially asleep
	_mma7260qt_wakeup(); //initially awake
	
}
