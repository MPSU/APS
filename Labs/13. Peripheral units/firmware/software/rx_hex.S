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
 0: 050000b7       li x1 , 0x05000000          # save UART RX base address
 4: 04000137       li x2 , 0x04000000          # save hex-controller base address
 8: 0001c1b7       li x3 , 0x0001c200          # set baud rate to 115200
 c: 20018193
10: 0030a623       sw x3 , 0x0c(x1)
14: 00100213       li x4 , 0x00000001          # set parity bit
18: 0040a823       sw x4 , 0x10(x1)
1c: 03400293       la x5, trap_handler         # the la pseudo-instruction loads a number similarly to li,
20: 00028293                                   # but in the case of la the number is the address
                                               # of the specified location (the trap handler address);
                                               # this pseudo-instruction will be split into two
                                               # instructions: lui and addi
24: 30529073       csrw mtvec, x5              # set the interrupt vector
28: 000102b7       li x5 , 0x00010000          # prepare the interrupt mask for the single
                                               # (zeroth) input
2c: 30429073       csrw mie, x5                # load the mask into the mask register

# Call main function
main:
30: 00000063       beq x0, x0, main            # infinite loop, equivalent to while (1);
# TRAP HANDLER
# Without external intervention the processor will never reach the instructions below;
# however, upon an interrupt the program counter will be loaded with the address of
# the first instruction below.
# Save used registers to the stack
trap_handler:
34: 0000a383       lw x7, 0(x1)                # load the received byte
38: 00700333       add x6, x0, x7              # duplicate the scan code
3c: 00435313       srl x6, x6, 4               # shift right by 4 to obtain the upper nibble
40: 00612223       sw  x6, 4(x2)               # write upper nibble to the first seven-segment display
44: 00f3f393       andi x7, x7, 0xf            # mask with f to obtain the lower nibble
48: 00712023       sw  x7,  0(x2)              # write lower nibble to the zeroth seven-segment display
4c: 30200073       mret
