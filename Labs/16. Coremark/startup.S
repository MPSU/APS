/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
  .section    .boot

 .global _start
_start:
  la    gp, _gbl_ptr     # Initialize the global pointer
  la    sp, _stack_ptr   # Initialize the stack pointer

# Initialize (zero out) the bss segment
  la    t0, _bss_start
  la    t1, _bss_end
_bss_init_loop:
  blt   t1, t0, _irq_config
  sw    zero, 0(t0)
  addi  t0, t0, 4
  j     _bss_init_loop

# Configure the interrupt vector (mtvec), interrupt mask (mie),
# and trap stack pointer (mscratch).
_irq_config:
  la    t0, _int_handler
  li    t1, -1 # -1 (all bits set to 1) means all interrupts are enabled
  la    t2, _trap_stack_ptr
  csrw  mtvec, t0
  csrw  mscratch, t2
  csrw  mie, t1

# Call the main function
_main_call:
  li    a0, 0 # Pass argc and argv arguments to main. Formally, argc should
  li    a1, 0 # be greater than zero, and argv should point to an array of
              # strings whose zeroth element is the executable name.
              # For simplicity of implementation, both arguments are simply
              # set to zero. This is done for deterministic program behavior
              # in case the programmer tries to use these arguments.

  # Call main.
  # For the program to link successfully, a function with exactly
  # this name must be defined somewhere.
  call  main
# Infinite loop after main returns
_endless_loop:
  j     _endless_loop

# The low-level interrupt handler is responsible for:
#   * Saving and restoring context;
#   * Calling the high-level handler with the interrupt source id
#     as an argument.
# The code is based on the handler from the urv-core repository:
# https://github.com/twlostow/urv-core/blob/master/sw/common/irq.S
# Saves of unimplemented CS registers have been removed. Additionally,
# only caller-saved registers are saved here, because the high-level
# interrupt handler is required to preserve callee-saved registers
# in accordance with the calling convention.
_int_handler:
  # This operation swaps the sp and mscratch registers.
  # As a result, the trap stack pointer ends up in sp, and the top
  # of the program stack ends up in mscratch.
  csrrw sp, mscratch,sp

  # Move up the trap stack and save all registers.
  addi  sp, sp, -80  # The stack pointer must be aligned to 16 bytes,
                     # so we move up by 80, not 76.
  sw    ra, 4(sp)
  # We want to ensure that a subsequent interrupt does not cause the trap
  # stack to overwrite the program stack, so we load the bottom of the
  # program stack into the freed register and verify that the raised trap
  # stack pointer has not encroached on the program stack.
  # If this has happened (trap stack overflow), we want to halt the
  # processor to avoid losing data that could help us debug the situation.
  la    ra, _stack_ptr
  blt   sp, ra, _endless_loop

  sw    t0, 12(sp) # We skipped offset 8 because that is where the sp
                   # register saved into mscratch earlier should go.
                   # We will write it to the stack a little later.
  sw    t1, 16(sp)
  sw    t2, 20(sp)
  sw    a0, 24(sp)
  sw    a1, 28(sp)
  sw    a2, 32(sp)
  sw    a3, 36(sp)
  sw    a4, 40(sp)
  sw    a5, 44(sp)
  sw    a6, 48(sp)
  sw    a7, 52(sp)
  sw    t3, 56(sp)
  sw    t4, 60(sp)
  sw    t5, 64(sp)
  sw    t6, 68(sp)

  # We also save the interrupt register state in case another
  # interrupt occurs.
  csrr  t0, mscratch
  csrr  t1, mepc
  csrr  a0, mcause
  sw    t0, 8(sp)
  sw    t1, 72(sp)
  sw    a0, 76(sp)

  # Call the high-level interrupt handler.
  # For the program to link successfully, a function with exactly
  # this name must be defined somewhere.
  call  int_handler

  # Restore context. First, we want to restore the CS registers in case
  # a nested interrupt occurred. To do this, we must restore the original
  # value of the trap stack pointer. However, its current value is still
  # needed for context restoration, so we save it to register a0 and
  # restore from there.
  mv    a0,sp

  lw    t1, 72(a0)
  lw    t2, 76(a0)
  addi  sp, sp, 80
  csrw  mscratch, sp
  csrw  mepc, t1
  csrw  mcause, t2
  lw    ra, 4(a0)
  lw    sp, 8(a0)
  lw    t0, 12(a0)
  lw    t1, 16(a0)
  lw    t2, 20(a0)
  lw    a1, 28(a0)   # We skipped a0 because it is currently used as a
                     # pointer to the top of the stack and cannot be
                     # restored.
  lw    a2, 32(a0)
  lw    a3, 36(a0)
  lw    a4, 40(a0)
  lw    a5, 44(a0)
  lw    a6, 48(a0)
  lw    a7, 52(a0)
  lw    t3, 56(a0)
  lw    t4, 60(a0)
  lw    t5, 64(a0)
  lw    t6, 68(a0)
  lw    a0, 24(a0)

  # Return from the interrupt handler
  mret
