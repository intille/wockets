#include <avr/io.h>
#include <util/delay.h>
#include "avr_general.h"
#include "bt_rn41.h"

void _rn41_init(){
	//set status pins as input
	cbi(DDRD,BT_DISCOVERABLE_PIN);
	cbi(DDRD,BT_CONNECTED_PIN);
	cbi(DDRD,BT_RX_PIN);
	sbi(DDRD,BT_TX_PIN);


	sbi(DDRD,BT_RESET_PIN);

	//set RX and Reset PINS as output
	sbi(PORTD,BT_RESET_PIN);  //turn on bt
	sbi(DDRB,BT_SW);
	cbi(PINB,BT_SW);

}


unsigned char _rn41_is_connected(){

	return (0x01 & (PIND>>BT_CONNECTED_PIN));


}


unsigned char _rn41_is_discoverable(){

	return (0x01 & (PIND>>BT_DISCOVERABLE_PIN));
}


void _rn41_off(){		
	cbi(PORTD,BT_RESET_PIN);  //turn off bt via switch
}

void _rn41_on(){
	sbi(PORTD,BT_RESET_PIN);
}

void _rn41_reset(){
	_rn41_off();
	_delay_ms(100);	
	_rn41_on();
	//cbi(PORTD,BT_RESET_PIN);
	//_delay_ms(100);
	//sbi(PORTD,BT_RESET_PIN);
}
