# Testing CYBERcobra on FPGA

After verifying the design in simulation, you need to test it on an FPGA prototype.

Instructions for implementing the prototype are described [here](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

_Fig. 1_ shows the prototype schematic on the FPGA.

![../../../.pic/Labs/board%20files/nexys_cobra_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_cobra_structure.drawio.svg)

_Figure 1. Block diagram of the `nexys_CYBERcobra` module._

The prototype allows you to execute the program stored in the instruction memory one clock cycle at a time. It also displays the operation currently being executed by the processor.

> [!NOTE]
> The instance of the `instr_mem` module inside `CYBERcobra` **must** be named `imem`. That is, the instantiation line must look like this: `instr_mem imem(...)`.

## Peripheral Description

-   ### Switches

    The values of switches `SW[15:0]` are passed directly to the `sw_i` port of the design module.

-   ### Buttons

    -   `BTND` — pressing this button generates a clock pulse delivered to the `clk_i` port of the design module.
    -   `CPU_RESET` — connected to the `rst_i` input of the design module. Since `CYBERcobra` uses synchronous reset (i.e., the reset signal is only recognized on a rising clock edge), resetting the `CYBERcobra` module and its sub-modules requires holding down the reset button and then pressing the clock button.

-   ### LEDs

    LEDs `LED[15:0]` display the lower 16 bits of the value currently present on the `out_o` port of the design module.

-   ### Seven-Segment Displays

    The seven-segment displays are divided into 3 blocks (see _Fig. 1_):

    -   `out` — displays the lower 8 bits of the value on the `out_o` port of the design module as a hexadecimal number.
    -   `PC` — displays the lower 8 bits of the program counter, which is driven to the `addr_i` input of the instruction memory module, as a hexadecimal number.
    -   `operation` — displays the [operation](#Operations-displayed-by-the-prototype) currently being executed by the processor.

## Operations Displayed by the Prototype

Mapping of instruction types to displayed operations:

1.  Computational instructions — corresponds to the opcodes of ALU computational operations.
1.  Load-immediate instruction — `LI` (from **l**oad **i**mmediate).
1.  Load-from-external-device instruction — `IN` (from **in**put).
1.  Unconditional jump — `JUMP`.
1.  Conditional branch instructions — corresponds to the opcodes of ALU comparison operations.

During the execution of computational instructions and conditional branch instructions, illegal operations may be encountered (displayed as `ILL`, from **ill**egal). An operation is considered illegal in the following cases:

-   If the ALU operation field of the instruction contains a bit pattern that is not within the range of valid values.
-   If the instruction is a computational instruction but the ALU operation field contains a bit pattern corresponding to a flag-computing operation, or vice versa.

The instruction `0 0 11 xxxxxxxxxxxxxxxxxxxxxxxxxxxx` is displayed as `NOP` (from **n**o **op**eration).

The mapping of operations to their representation on the seven-segment displays is shown in _Fig. 2_:

!['../../../.pic/Labs/board%20files/nexys_cobra_operations.drawio.svg'](../../../.pic/Labs/board%20files/nexys_cobra_operations.drawio.svg)

_Figure 2. Mapping of operations to their representation on the seven-segment displays._


## Demo Program

The recommended demo program is [program.mem](../program.mem). A description of how it works can be found in the [#final-overview](../#Final-overview) section.
