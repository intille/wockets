
#define PRESCALAR_2 0
#define PRESCALAR_4 1
#define PRESCALAR_8 2
#define PRESCALAR_16 3
#define PRESCALAR_32 4
#define PRESCALAR_64 5
#define PRESCALAR_128 6

#define ADC0 0
#define ADC1 1
#define ADC2 2
#define ADC3 3

//#define ADC3 3

//LED CONTROL PORT C
#define GREEN_LED 1
#define YELLOW_LED 2

void _atmega324p_init();
void _atmega324p_green_led_on();
void _atmega324p_green_led_off();
void _atmega324p_yellow_led_on();
void _atmega324p_yellow_led_off();
void _atmega324p_init_uart0(unsigned int baud);
void _atmega324p_init_adc();
void _atmega324p_set_prescalar_adc(unsigned char prescalar);
void _atmega324p_set_reference_adc();
void _atmega324p_set_channel_adc(unsigned char channel);
unsigned short  _atmega324p_a2dConvert10bit(unsigned char ch);
unsigned char ReceiveByte( void );
void TransmitByte( unsigned char data );



