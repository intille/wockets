#include <avr/io.h>
#include "avr_general.h"
#include "bt_rn41.h"

void _rn41_init(){
	//set status pins as input
	cbi(DDRD,BT_DISCOVERABLE_PIN);
	cbi(DDRD,BT_CONNECTED_PIN);
	cbi(DDRD,BT_RX_PIN);

	//set RX and Reset PINS as output
	sbi(DDRD,BT_TX_PIN);
	sbi(PORTD,BT_RESET_PIN);  //turn on bt

}


unsigned char _rn41_is_connected(){

	return (0x01 & (PIND>>BT_CONNECTED_PIN));


}


unsigned char _rn41_is_discoverable(){

	return (0x01 & (PIND>>BT_DISCOVERABLE_PIN));
}


void rn_41_off(){
	sbi(PORTB, BT_SW);  //turn off bt via switch
}

void rn_41_on(){
	cbi(PORTB, BT_SW);
}

void _rn41_reset(){
	cbi(PORTD,BT_RESET_PIN);
	sbi(PORTD,BT_RESET_PIN);
}
