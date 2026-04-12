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
 0: 050000b7      li x1 , 0x05000000          # save UART RX base address
 4: 06000137      li x2 , 0x06000000          # save UART TX base address
 8: 0001c1b7      li x3 , 0x0001c200          # set baud rate to 115200
 c: 20018193
10: 0030a623      sw x3 , 0x0c(x1)
14: 00312623      sw x3 , 0x0c(x2)
18: 00100213      li x4 , 0x00000001          # set parity bit
1c: 0040a823      sw x4 , 0x10(x1)
20: 00412823      sw x4 , 0x10(x2)
24: 03c00293      la x5, trap_handler         # the la pseudo-instruction loads a number similarly to li,
28: 00028293                                  # but in the case of la the number is the address
                                              # of the specified location (the trap handler address);
                                              # this pseudo-instruction will be split into two
                                              # instructions: lui and addi
2c: 30529073      csrw mtvec, x5              # set the interrupt vector
30: 000102b7      li x5 , 0x00010000          # prepare the interrupt mask for the single
                                              # (zeroth) input
34: 30429073      csrw mie, x5                # load the mask into the mask register

# Call main function
main:
38: 00000063      beq x0, x0, main            # infinite loop, equivalent to while (1);
# TRAP HANDLER
# Without external intervention the processor will never reach the instructions below;
# however, upon an interrupt the program counter will be loaded with the address of
# the first instruction below.
# Save used registers to the stack
trap_handler:
3c: 0000a383      lw x7, 0(x1)                # load the received byte
40: 00712023      sw x7, 0(x2)
44: 30200073      mret
