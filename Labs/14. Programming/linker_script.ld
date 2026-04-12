/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

OUTPUT_FORMAT("elf32-littleriscv")      /* Specify the byte order */

ENTRY(_start)                           /* We tell the linker that the first
                                           instruction executed by the processor
                                           is at the label "_start"
                                        */

/*
  This section specifies the memory structure:
  First comes the "instr_mem" region, which is executable memory
  (indicated by the 'x' attribute). This region starts
  at address 0x00000000 and occupies 1024 bytes.
  Next comes the "data_mem" region, starting at address 0x00000000 and
  occupying 2048 bytes. This region is non-executable memory
  (in the sense that it does not contain executable code).
*/
MEMORY
{
  instr_mem (x) : ORIGIN = 0x00000000, LENGTH = 1K
  data_mem (!x) : ORIGIN = 0x00000000, LENGTH = 2K
}

_trap_stack_size = 640;                /* Size of the trap handler stack.
                                          This size allows up to 8 nested
                                          calls during trap handling.
                                        */

_stack_size = 640;                     /* Size of the program stack.
                                          This size allows up to 8 nested
                                          calls.
                                       */

/*
  This section describes the placement of the program in memory.
  The program is divided into various sections:
  - sections of the executable code;
  - sections of static variables and arrays whose values must be
    embedded in the program;
  etc.
*/

SECTIONS
{

  /*
    In linker scripts there is an internal variable written as '.'
    This variable is called the "location counter". It stores the current
    address in memory.
    At the beginning of the file it is initialized to zero. As new sections
    are added, this variable is incremented by the size of each new section.
    If no address is specified when placing sections, they will be placed
    at the current value of the location counter.
    This variable can be assigned values; after that, it will increment
    from that value.
    More details:
      https://home.cs.colorado.edu/~main/cs1300/doc/gnu/ld_3.html#IDX338
  */

  /*
    The following command specifies that starting from the address currently
    held by the location counter (at this point, starting from zero), the
    .text section of the output file will be located, consisting of the .boot
    sections as well as all sections starting with .text from all binary files
    passed to the linker.
    We additionally specify that this section must be placed in the
    "instr_mem" region.
  */
  .text : {
    PROVIDE(_start = .);
    *(.boot)
    *(.text*)
  } > instr_mem


  /*
  The data section is placed similarly to the instruction section, except
  for the Load Memory Address (LMA). Since instruction and data memories are
  physically separate, they have overlapping address spaces that we would
  like to use (which is why in the MEMORY section we set the start addresses
  of both memories to zero). However, the linker does not like this, since
  how can it place two different sections in the same location? So we tell it,
  using the "AT" operator, that the data section should actually be loaded
  at a different address — one that is guaranteed to be larger than the size
  of the instruction memory — while the processor will use addresses starting
  from zero. The linker accepts this arrangement and builds the executable
  without errors. Our task is then to load the final data section at address
  zero in data memory.
  */
  .data : AT (0x00800000) {
    /*
    It is conventional to assign GP a value equal to the start of the data
    section offset forward by 2048 bytes.
    With 12-bit relative addressing with offset, it is possible to address
    the beginning of the data section as well as the entire address space up
    to 4096 bytes from the start of the data section, which reduces the number
    of addressing instructions needed (LUI operations are rarely used since GP
    already holds the base address and only an offset is needed).
    More details:
      https://groups.google.com/a/groups.riscv.org/g/sw-dev/c/60IdaZj27dY/m/s1eJMlrUAQAJ
    */
    _gbl_ptr = . + 2048;
    *(.*data*)
    *(.sdata*)
  } > data_mem


  /*
    Since we do not know the total size of all data sections used,
    before placing other sections, we must align the location counter
    to a 4-byte boundary.
  */
  . = ALIGN(4);


  /*
    BSS (block started by symbol, unofficially expanded as
    "better save space") is a segment where uninitialized static
    variables are placed. The C standard states that such variables
    are initialized to zero (or NULL for pointers). When you create
    a static array, it must be placed in the executable file.
    Without a bss section, the array would occupy as much space in the
    executable as its own size. A 1000-byte array would take 1000 bytes
    in the .data section.
    Thanks to the bss section, the initial values of the array are not stored;
    instead, only the variable names and their addresses are recorded.
    However, during executable loading, the memory region occupied by the
    bss section must be explicitly zeroed out, since static variables must
    be initialized to zero.
    Thus, the bss section significantly reduces the size of the executable
    (when using uninitialized static arrays) at the cost of increased
    loading time.
    To zero out the bss section, two variables are defined in the script
    that point to the beginning and end of the bss section via the
    location counter.
    More details:
      https://en.wikipedia.org/wiki/.bss

    We additionally specify that this section must be placed in the
    "data_mem" region.
  */
  _bss_start = .;
  .bss : {
    *(.bss*)
    *(.sbss*)
  } > data_mem
  _bss_end = .;


  /*=================================
      The allocated data section is complete; the remaining free memory is
      reserved for the program stack, the trap stack, and (possibly) the heap.
      The RISC-V calling convention states that the stack grows downward
      (from higher to lower addresses), so our goal is to place it at the
      highest addresses in memory.
      Since we have two stacks, the trap stack is placed at the very bottom
      and the program stack above it. We must also ensure that the program
      stack is protected from being overwritten by the trap stack.
      Before doing so, however, we must verify that there is enough room
      for both stacks.
    =================================
  */

  /* We want to guarantee that there is room left for the stack */
  ASSERT(. < (LENGTH(data_mem) - _trap_stack_size - _stack_size),
            "Program size is too big")

  /*  Move the location counter above the trap stack (so that we can
      use it in the ALIGN call later) */
  . = LENGTH(data_mem) - _trap_stack_size;

  /*
      Place the program stack pointer as close to the trap stack boundary
      as possible, subject to the requirement that the stack address be
      aligned to 16 bytes.
      More details:
        https://riscv.org/wp-content/uploads/2015/01/riscv-calling.pdf
  */
  _stack_ptr = ALIGN(16) <= LENGTH(data_mem) - _trap_stack_size?
                ALIGN(16) : ALIGN(16) - 16;
  ASSERT(_stack_ptr <= LENGTH(data_mem) - _trap_stack_size,
            "SP exceed memory size")

  /*  Move the location counter to the end of memory (so that we can
      use it in the ALIGN call later) */
  . = LENGTH(data_mem);

  /*
      Memory size is usually a multiple of 16, but in case it is not, we
      perform a check: we either stay at the very end of memory (if the
      end is a multiple of 16), or move 16 bytes up from the memory edge
      rounded up to the nearest multiple of 16.
  */
  _trap_stack_ptr = ALIGN(16) <= LENGTH(data_mem) ? ALIGN(16) : ALIGN(16) - 16;
  ASSERT(_trap_stack_ptr <= LENGTH(data_mem), "ISP exceed memory size")
}
