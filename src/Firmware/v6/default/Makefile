###############################################################################
# Makefile for the project wockets_firmware_avr
###############################################################################

## General Flags
PROJECT = wockets_firmware_avr
MCU = atmega1284p
TARGET = wockets_firmware_6.elf
CC = avr-gcc

CPP = avr-g++

## Options common to compile, link and assembly rules
COMMON = -mmcu=$(MCU)

## Compile options common for all C compilation units.
CFLAGS = $(COMMON)
CFLAGS += -Wall -gdwarf-2 -std=gnu99 -Os -funsigned-char -funsigned-bitfields -fpack-struct -fshort-enums
CFLAGS += -MD -MP -MT $(*F).o -MF dep/$(@F).d 

## Assembly specific flags
ASMFLAGS = $(COMMON)
ASMFLAGS += $(CFLAGS)
ASMFLAGS += -x assembler-with-cpp -Wa,-gdwarf2

## Linker flags
LDFLAGS = $(COMMON)
LDFLAGS +=  -Wl,-Map=wockets_firmware_6.map


## Intel Hex file production flags
HEX_FLASH_FLAGS = -R .eeprom -R .fuse -R .lock -R .signature

HEX_EEPROM_FLAGS = -j .eeprom
HEX_EEPROM_FLAGS += --set-section-flags=.eeprom="alloc,load"
HEX_EEPROM_FLAGS += --change-section-lma .eeprom=0 --no-change-warnings


## Objects that must be built in order to link
OBJECTS = crc.o firmware-version_6.o mcu_atmega.o wocket.o 

## Objects explicitly added by the user
LINKONLYOBJECTS = 

## Build
all: $(TARGET) wockets_firmware_6.hex wockets_firmware_6.eep wockets_firmware_6.lss size

## Compile
crc.o: ../crc.c
	$(CC) $(INCLUDES) $(CFLAGS) -c  $<

firmware-version_6.o: ../firmware-version_6.c
	$(CC) $(INCLUDES) $(CFLAGS) -c  $<

mcu_atmega.o: ../mcu_atmega.c
	$(CC) $(INCLUDES) $(CFLAGS) -c  $<

wocket.o: ../wocket.c
	$(CC) $(INCLUDES) $(CFLAGS) -c  $<

##Link
$(TARGET): $(OBJECTS)
	 $(CC) $(LDFLAGS) $(OBJECTS) $(LINKONLYOBJECTS) $(LIBDIRS) $(LIBS) -o $(TARGET)

%.hex: $(TARGET)
	avr-objcopy -O ihex $(HEX_FLASH_FLAGS)  $< $@

%.eep: $(TARGET)
	-avr-objcopy $(HEX_EEPROM_FLAGS) -O ihex $< $@ || exit 0

%.lss: $(TARGET)
	avr-objdump -h -S $< > $@

size: ${TARGET}
	@echo
	@avr-size -C --mcu=${MCU} ${TARGET}

## Clean target
.PHONY: clean
clean:
	-rm -rf $(OBJECTS) wockets_firmware_6.elf dep/* wockets_firmware_6.hex wockets_firmware_6.eep wockets_firmware_6.lss wockets_firmware_6.map


## Other dependencies
-include $(shell mkdir dep 2>NUL) $(wildcard dep/*)

