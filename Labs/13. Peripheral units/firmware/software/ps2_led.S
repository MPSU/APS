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
 0: 030000b7       li x1 , 0x03000000      # save keyboard base address
 4: 02000137       li x2 , 0x02000000      # save LED controller base address
 8: 0e000193       li x3 , 0x000000e0      # save scan code e0
0с: 00000593       li x11, 0x00000000      # save zero
10: 02800293       la x5, trap_handler     # the la pseudo-instruction loads a number similarly to li,
14: 00028293                               # but in the case of la the number is the address
                                           # of the specified location (the trap handler address);
                                           # this pseudo-instruction will be split into two
                                           # instructions: lui and addi
18: 30529073       csrw mtvec, x5          # set the interrupt vector
1c: 000102b7       li x5 , 0x00010000      # prepare the interrupt mask for the single
                                           # (zeroth) input
20: 30429073       csrw mie, x5            # load the mask into the mask register

# Call main function
main:
24: 00000063       beq x0, x0, main        # infinite loop, equivalent to while (1);

# TRAP HANDLER
# Without external intervention the processor will never reach the instructions below;
# however, upon an interrupt the program counter will be loaded with the address of
# the first instruction below.
# Save used registers to the stack
trap_handler:
28: 0000a383       lw  x7, 0(x1)           # load scan code
2c: 00338663       beq x7, x3, change_mode # if scan code is e0, toggle LED mode
30: 00712023       sw  x7, 0(x2)           # output scan code to LEDs
34: 30200073       mret                    # return control to the program (pc = mepc),
                                           # which means returning to the infinite loop

change_mode:
38: 00412403       lw   x8, 4(x2)          # read the current mode value
3c: 00144413       xori x8, x8, 1          # invert its least significant bit
40: 00812223       sw   x8, 4(x2)          # write the inverted mode back
44: 30200073       mret                    # return control to the program (pc = mepc),
                                           # which means returning to the infinite loop
