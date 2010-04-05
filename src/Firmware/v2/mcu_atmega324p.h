#define OSCCAL_ADDRESS 0x0E

#define ATMEGA324P_BAUD_2400 	207
#define ATMEGA324P_BAUD_4800 	103
#define ATMEGA324P_BAUD_9600 	51
#define ATMEGA324P_BAUD_19200 	25
#define ATMEGA324P_BAUD_28800	16
#define ATMEGA324P_BAUD_38400 	12
#define ATMEGA324P_BAUD_57600	8
#define ATMEGA324P_BAUD_115200	3
#define ATMEGA324P_BAUD_230000	1
#define ATMEGA324P_BAUD_460000	0



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
#define ADC4 4
#define ADC6 6
#define ADC7 7


#define ENABLE_SLEEP 0
#define SLEEP1 1
#define SLEEP2 2
#define SLEEP3 3

#define USER_BUTTON_PIN 5

//#define ADC3 3

//LED CONTROL PORT C
#define GREEN_LED 1
#define YELLOW_LED 2



//UART supported baud rates

#define ATMEGA_BAUD_2400 	207
#define ATMEGA_BAUD_4800 	103
#define ATMEGA_BAUD_9600 	51
#define ATMEGA_BAUD_19200 	25
#define ATMEGA_BAUD_28800	16
#define ATMEGA_BAUD_38400 	12
#define ATMEGA_BAUD_57600	8
#define ATMEGA_BAUD_115200	3
#define ATMEGA_BAUD_230000	1
#define ATMEGA_BAUD_460000	0

//UART Modes
#define TX_UART_MODE 0
#define RX_UART_MODE 1
#define TX_RX_UART_MODE 2


// Port Definitions
// Port A
#define IN_VSENSE_COMP_PA0 0
#define IN_ACCEL_Z_FILT_PA1 1
#define IN_ACCEL_Y_FILT_PA2 2
#define IN_ACCEL_X_FILT_PA3 3
#define IN_VSENSE_BAT_PA4 4
#define IN_USER_N_PA5 5
#define FLOAT_PA6 6
#define FLOAT_PA7 7

// Port B
#define OUT_ACCEL_SEL1_PB0 0
#define OUT_ACCEL_SEL2_PB1 1
#define IN_VSENSE_COMP_PB2 2
#define OUT_ACCEL_SLEEP_N_PB3 3
#define OUT_BT_SW_N_PB4 4
#define IN_CPU_PROG_MOSI_PB5 5
#define OUT_CPU_PROG_MISO_PB6 6
#define IN_CPU_PROG_SCLK_PB7 7

// Port C
#define FLOAT_PC0 0
#define OUT_LED_GN_PC1 1
#define OUT_LED_YE_PC2 2
#define FLOAT_PC3 3
#define FLOAT_PC4 4
#define FLOAT_PC5 5
#define FLOAT_PC6 6
#define FLOAT_PC7 7

// Port D
#define IN_BT_RXD_PD0 0
#define OUT_BT_TXD_PD1 1
#define OUT_BT_RESET_N_PD2 2
#define IN_VIB_SW_N_PD3 3
#define IN_BT_CONNECT_PD4 4
#define IN_BT_DISC_PD5 5
#define FLOAT_PD6 6
#define FLOAT_PD7 7


/*  Accelerometer Constants */
#define _1_5G 0
#define _2G 1
#define _4G 2
#define _6G 3


/* Wocket Status Bits Constants */

#define BIT0_BLUETOOTH_STATUS  0
#define BIT1_ACCELEROMETER_STATUS 1
#define BIT2_GREENLED_STATUS 2
#define BIT3_YELLOWLED_STATUS 3
#define BIT4_MASTERSLAVE_STATUS 4

//ADC Prescalars

#define ADC_PRESCALAR_2 0
#define ADC_PRESCALAR_4 1
#define ADC_PRESCALAR_8 2
#define ADC_PRESCALAR_16 3
#define ADC_PRESCALAR_32 4
#define ADC_PRESCALAR_64 5
#define ADC_PRESCALAR_128 6


#define CPU_CLK_PRESCALAR_NONE 0
#define CPU_CLK_PRESCALAR_8 1
#define CPU_CLK_PRESCALAR_32 2
#define CPU_CLK_PRESCALAR_64 3
#define CPU_CLK_PRESCALAR_128 4
#define CPU_CLK_PRESCALAR_256 5
#define CPU_CLK_PRESCALAR_1024 6

/* Exported Function Prototypes */

/* MCU Specific Functions */
void _atmega_initialize(unsigned char timer_prescalar);
void _atmega_disable_JTAG(void);
void _atmega_disable_watchdog(void);
void _atmega_enable_timer2(unsigned char timer_prescalar);
void _atmega_disable_timer2(void);
void _atmega_finalize(void);
void _atmega_initialize_uart0(unsigned int baud, unsigned char mode);
void _atmega_initialize_uart1(unsigned int baud, unsigned char mode);
unsigned short _atmega_a2dConvert10bit(unsigned char channel);
void _atmega_reset(void);


/* LED Specific Functions */
void _greenled_turn_on(void);
void _greenled_turn_off(void);
unsigned char _is_greenled_on(void);

void _yellowled_turn_on(void);
void _yellowled_turn_off(void);
unsigned char _is_yellowled_on(void);

/* Bluetooth Specific Functions */

unsigned char _bluetooth_initialize(unsigned baudrate);
unsigned char _bluetooth_enter_command_mode(void);
unsigned char _bluetooth_exit_command_mode(void);
void _bluetooth_reset(void);
unsigned char _bluetooth_get_baud_rate();
unsigned char _bluetooth_set_baud_rate(unsigned char baudrate);
void _bluetooth_turn_on(void);
void _bluetooth_turn_off(void);
unsigned char _is_bluetooth_on(void);
unsigned char _bluetooth_is_connected(void);
unsigned char _bluetooth_is_discoverable(void);
void _bluetooth_transmit_uart0_byte(unsigned char data);
unsigned char _bluetooth_receive_uart0_byte(unsigned char *data);

/* Accelerometer Specific Functions */
unsigned char _accelerometer_set_sensitivity(unsigned char sensitivity);
void _accelerometer_turn_on(void);
void _accelerometer_turn_off(void);
unsigned char _is_accelerometer_on(void);

//The variable stores the status for different wocket priephrals
unsigned char wocket_status;
unsigned char atmega_clock_prescalar;

void _atmega324p_init();
void _atmega324p_green_led_on();
void _atmega324p_green_led_off();
void _atmega324p_yellow_led_on();
void _atmega324p_yellow_led_off();
void _atmega324p_power_down();
void _atmega324p_init_uart0(unsigned int baud);
void _atmega324p_init_adc();
void _atmega324p_reset();
void _atmega324p_set_prescalar_adc(unsigned char prescalar);
void _atmega324p_set_reference_adc();
void _atmega324p_set_channel_adc(unsigned char channel);
unsigned short  _atmega324p_a2dConvert10bit(unsigned char ch);
unsigned char ReceiveByte(unsigned char *data);
void TransmitByte( unsigned char data );
unsigned char _atmega324p_shutdown();


