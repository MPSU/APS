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
 0: 030000b7        li x1, 0x03000000           # save keyboard base address
 4: 07000137        li x2, 0x07000000           # save VGA controller base address
 8: 070011b7        li x3, 0x07000960           # total number of characters on screen
 c: 96018193                                    # this pseudo-instruction will be split into two
                                                # instructions: lui and addi
10: 02400293        la x5, trap_handler         # the la pseudo-instruction loads a number similarly to li,
                                                # but in the case of la the number is the address
                                                # of the specified location (the trap handler address)
14: 30529073        csrw mtvec, x5              # set the interrupt vector
18: 000102b7        li x5 , 0x00010000          # prepare the interrupt mask for the single
                                                # (zeroth) input
1c: 30429073        csrw mie, x5               # load the mask into the mask register

# Call main function
main:
20:	00000063        beq x0, x0, main            # infinite loop, equivalent to while (1);

# TRAP HANDLER
# Without external intervention the processor will never reach the instructions below;
# however, upon an interrupt the program counter will be loaded with the address of
# the first instruction below.
# Save used registers to the stack
trap_handler:
24: 0000a383        lw x7, 0(x1)                # load scan code
28: 00038403        lb x8, 0(x7)                # fetch data from the lookup table
2c: 00810023        sb x8, 0(x2)                # write ASCII value to VGA
30: 00110113        addi x2, x2, 1              # increment VGA address
34: 00315463        bge x2, x3, wrap_addr       # if VGA address is out of bounds, wrap it
38: 30200073        mret                        # return control to the program (pc = mepc),
                            # which means returning to the infinite loop
wrap_addr:
3c: 07000137        li x2, 0x07000000           # restore VGA controller base address
40: 30200073        mret
