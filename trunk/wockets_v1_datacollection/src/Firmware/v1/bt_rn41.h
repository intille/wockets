/*** PORTC PINs for accelerometer settings ***/





//port D
#define BT_RX_PIN 0
#define BT_TX_PIN 1
#define BT_RESET_PIN 2
#define BT_DISCOVERABLE_PIN 5  //set as input
#define BT_CONNECTED_PIN 4  //set as input

//Port B
#define BT_SW 4

void _rn41_init();
unsigned char _rn41_is_connected();
unsigned char _rn41_is_discoverable();
void _rn41_off();
void _rn41_on();
void _rn41_reset();

