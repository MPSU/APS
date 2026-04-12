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
  0: 010000b7        li x1, 0x01000000          # save switches base address
  4: 02000137        li x2, 0x02000000          # save LED controller base address
  8: 0000b1b7        li x3, 0x0000aaaa          # save special code for blink mode
  c: aaa18193
 10: 00005237       li x4, 0x00005555           # save special code for reset
 14: 55520213
 18: 00100313       li x6, 0x00000001           # save one
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
 34: 0000a383       lw x7, 0(x1)                # load the value from the switches
 38: 00338863       beq x7, x3, blink_mode      # if blink special code received, jump to blink_mode
 3c: 00438a63       beq x7, x4, reset           # if reset special code received, jump to reset
 40: 00712023       sw x7, 0(x2)                # write the switch value to LEDs
 44: 30200073       mret                        # return control to the program (pc = mepc),
                                                # which means returning to the infinite loop
blink_mode:
 48:	00612223      sw x6, 4(x2)                # write 1 to led_mode
 4c:	30200073      mret

reset:
 50:	02612223      sw x6, 0x24(x2)             # write 1 to led_reset
 54:	30200073      mret
