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
 4: 04000137       li x2 , 0x04000000      # save hex-controller base address
 8: 0e000193       li x3 , 0x000000e0      # save scan code e0
 c: 0f000213       li x4 , 0x000000f0      # save scan code f0
10: 00e00413       li x8 , 0x0000000e      # save value e
14: 00f00493       li x9 , 0x0000000f      # save value f
18: 00000593       li x11, 0x00000000      # save zero
1c: 03400293       la x5, trap_handler     # the la pseudo-instruction loads a number similarly to li,
20: 00028293                               # but in the case of la the number is the address
                                           # of the specified location (the trap handler address);
                                           # this pseudo-instruction will be split into two
                                           # instructions: lui and addi
24: 30529073       csrw mtvec, x5          # set the interrupt vector
28: 000102b7       li x5 , 0x00010000      # prepare the interrupt mask for the single
                                           # (zeroth) input
2c: 30429073       csrw mie, x5            # load the mask into the mask register

# Call main function
main:
30: 00000063       beq x0, x0, main        # infinite loop, equivalent to while (1);

# TRAP HANDLER
# Without external intervention the processor will never reach the instructions below;
# however, upon an interrupt the program counter will be loaded with the address of
# the first instruction below.
# Save used registers to the stack
trap_handler:
34: 0000a383       lw x7, 0(x1)            # load scan code
38: 04338263       beq x7, x3, print_e0    # if scan code is e0, display using print_e0
3c: 04438c63       beq x7, x4, print_f0    # if scan code is f0, display using print_f0
40: 00700333       add x6, x0, x7          # duplicate scan code
44: 00435313       srl x6, x6, 4           # shift right by 4 to obtain the upper nibble
48: 00612223       sw  x6, 4(x2)           # write upper nibble to the first seven-segment display
4c: 00f3f393       andi x7, x7, 0xf        # mask with f to obtain the lower nibble
50: 00712023       sw  x7,  0(x2)          # write lower nibble to the zeroth seven-segment display
54: 00b04c63       blt x0, x11, print_code # skip clearing of the upper hex displays
58: 00012a23       sw  x0, 20(x2)
5c: 00012823       sw  x0, 16(x2)          # clear seven-segment displays 2–5
60: 00012623       sw  x0, 12(x2)
64: 00012423       sw  x0,  8(x2)
68: 00300513       addi x10, x0, 3

print_code:
6c: 000005b3       add x11, x0, x0         # reset the counter
70: 00356513       ori x10, x10, 3         # initialize the mask enabling the 2 lower hex displays
74: 02a12023       sw  x10, 32(x2)         # write the mask
78: 30200073       mret                    # return control to the program (pc = mepc),
                                           # which means returning to the infinite loop
print_e0:
7c: 00812a23       sw x8, 20(x2)           # write e to the 5th seven-segment display
80: 00012823       sw x0, 16(x2)           # write 0 to the 4th seven-segment display
84: 03056513       ori x10, x10, 0x30      # enable display of hex digits 4–5 in the mask
88: 02a12023       sw  x10, 32(x2)         # write the mask
8c: 00158593       addi x11, x11, 1        # increment the counter
90: 30200073       mret

print_f0:
94: 00912623       sw x9, 12(x2)           # write f to the 3rd seven-segment display
98: 00012423       sw x0, 8(x2)            # write 0 to the 2nd seven-segment display
9c: 00c56513       ori x10, x10, 0xc       # enable display of hex digits 2–3 in the mask
a0: 02a12023       sw  x10, 32(x2)         # write the mask
a4: 00158593       addi x11, x11, 1        # increment the counter
a8: 30200073       mret
