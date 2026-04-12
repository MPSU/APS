/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
_start:
# Initialize register values
 0:	050000b7      li x1, 0x05000000           # save UART RX base address
 4:	02000137      li x2, 0x02000000           # save LED controller base address
 8:	0001c1b7      li x3, 0x0001c200           # set baud rate to 115200
 c:	20018193
10:	0030a623      sw x3, 0x0c(x1)
14:	00100213      li x4, 0x00000001           # set parity bit
18:	0040a823      sw x4, 0x10(x1)
1c:	000011b7      li x3, 0x00000D0D           # save special code for blink mode
20:	d0d18193
24:	00008237      li x4, 0x00000808           # save special code for reset
28:	f7f20213
2c:	0ff00493      li x9, 0x000000ff           # save mask for clearing the upper bytes
30:	00100313      li x6, 0x00000001           # save one
34:	04c00293      la x5, trap_handler         # the la pseudo-instruction loads a number similarly to li,
38:	00028293                                  # but in the case of la the number is the address
                                              # of the specified location (the trap handler address);
                                              # this pseudo-instruction will be split into two
                                              # instructions: lui and addi
3c:	30529073      csrw mtvec, x5              # set the interrupt vector
40:	000102b7      li x5 , 0x00010000          # prepare the interrupt mask for the single
                                              # (zeroth) input
44:	30429073      csrw mie, x5                # load the mask into the mask register

# Call main function
main:
48:	00000063      beq x0, x0, main            # infinite loop, equivalent to while (1);
# TRAP HANDLER
# Without external intervention the processor will never reach the instructions below;
# however, upon an interrupt the program counter will be loaded with the address of
# the first instruction below.
# Save used registers to the stack
trap_handler:
4c:	0000a383      lw x7, 0(x1)                # load value from UART RX
50:	00947433      and x8, x8, x9              # clear the upper 3 bytes
54:	00841413      slli x8, x8, 8              # shift register x8 left by 1 byte
58:	00746433      or x8, x8, x7              # write the byte read from RX into the vacated position
5c:	00340863      beq x8, x3, blink_mode      # if blink special code received, jump to blink_mode
60:	00440a63      beq x8, x4, reset           # if reset special code received, jump to reset
64:	00812023      sw x8, 0(x2)                # write the value to LEDs
68:	30200073      mret                        # return control to the program (pc = mepc),
                                              # which means returning to the infinite loop
blink_mode:
6c:	00612223      sw x6, 4(x2)                # write 1 to led_mode
70:	30200073      mret

reset:
74:	02612223      sw x6, 0x24(x2)             # write 1 to led_reset
78:	30200073      mret
