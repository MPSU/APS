# -----------------------------------------------------------------------------
# Project Name   : Architectures of Processor Systems (APS) lab work
# Organization   : National Research University of Electronic Technology (MIET)
# Department     : Institute of Microdevices and Control Systems
# Author(s)      : Andrei Solodovnikov
# Email(s)       : hepoh@org.miet.ru
#
# See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
# ------------------------------------------------------------------------------
#
CC_PATH = /c/riscv_cc/bin
CC_PREFIX = riscv-none-elf

CC      =   $(CC_PATH)/$(CC_PREFIX)-gcc
OBJDUMP =   $(CC_PATH)/$(CC_PREFIX)-objdump
OBJCOPY =   $(CC_PATH)/$(CC_PREFIX)-objcopy
SIZE    =   $(CC_PATH)/$(CC_PREFIX)-size

ifndef src
src = core_main.o
endif

OBJS = $(src) startup.o core_list_join.o core_matrix.o core_portme.o core_state.o core_util.o cvt.o ee_printf.o


LINK_SCRIPT = linker_script.ld
OUTPUT      = coremark
OUTPUT_PROD = $(addprefix $(OUTPUT), .mem _instr.mem _data.mem .elf _disasm.S)
# OUTPUT_PROD :=$(OUTPUT_PROD) $(addprefix tb_$(OUTPUT), .mem _instr.mem _data.mem .elf _disasm.S)

INC_DIRS    = "./"
SRC_DIR     = ./src
CC_FLAGS    = -march=rv32i_zicsr -mabi=ilp32 -I$(INC_DIRS)
LD_FLAGS    = -Wl,--gc-sections -nostartfiles -T $(LINK_SCRIPT)

.PHONY: all setup clean clean_all size harvard princeton

all: clean setup harvard

setup:
	cp barebones/*.c barebones/*.h ./

harvard: $(OUTPUT).elf $(OUTPUT)_disasm.S size
# $< означает "первая зависимость"
	${OBJCOPY} -O verilog --verilog-data-width=4 -j .data -j .sdata -j .bss $< $(OUTPUT)_data.mem
	${OBJCOPY} -O verilog --verilog-data-width=4 -j .text $< $(OUTPUT)_instr.mem
	${OBJCOPY} -O verilog -j .data -j .sdata -j .bss $< tb_$(OUTPUT)_data.mem
	${OBJCOPY} -O verilog -j .text $< tb_$(OUTPUT)_instr.mem
	sed -i '1d' $(OUTPUT)_data.mem

princeton: $(OUTPUT).elf $(OUTPUT)_disasm.S size
	${OBJCOPY} -O verilog --verilog-data-width=4 --remove-section=.comment $< $(OUTPUT).mem

$(OUTPUT).elf: $(OBJS)
# $^ Означает "все зависимости".
	${CC} $^ $(LD_FLAGS) $(CC_FLAGS) -o $(OUTPUT).elf

$(OUTPUT)_disasm.S: $(OUTPUT).elf
# $< означает "первая зависимость", $@ — "цель рецепта".
	${OBJDUMP} -D $< > $@


# Шаблонные рецепты (см. https://web.mit.edu/gnu/doc/html/make_10.html#SEC91)
# Здесь говорится как создать объектные файлы из одноименных исходников
%.o:	%.S
	${CC} -c $(CC_FLAGS) $^ -o $@

%.o:	%.c
	${CC} -c $(CC_FLAGS) $^ -o $@

%.o:	%.cpp
	${CC} -c $(CC_FLAGS) $^ -o $@

size: $(OUTPUT).elf
# $< означает "первая зависимость"
	$(SIZE) $<

clean:
	rm -f $(OBJS)
	rm -f core_portme.* cvt.c ee_printf.c

clean_all: clean
	rm -f $(OUTPUT_PROD)
