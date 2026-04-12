# Testing processor_system on FPGA

After verifying the design through simulation, you need to test it on an FPGA prototype.

Instructions for implementing the prototype are described [here](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

_Fig. 1_ shows the structure of the FPGA prototype.

![../../../.pic/Labs/board%20files/nexys_processor_system_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_processor_system_structure.drawio.svg)

_Figure 1. Block diagram of the `nexys_processor_system` module._

The prototype allows step-by-step execution of the program loaded into instruction memory. It also displays the operation currently being executed.

> [!NOTE]
> The instance of the `processor_core` module inside the `processor_system` module **must** be named `core`. That is, the instantiation line must look as follows: `processor_core core(...)`.

## Description of the peripherals used

-   ### Buttons

    -   `BTND` — when pressed, generates a clock pulse delivered to the `clk_i` port of the design module. Note that instructions that access external memory require several clock cycles to complete.
    -   `CPU_RESET` — connected to the `rst_i` input of the design module. Since `processor_system` uses synchronous reset (i.e., the reset signal is only sampled on the rising edge of the clock), resetting `processor_system` and its submodules requires holding the reset button while also pressing the clock button.

-   ### Seven-segment displays

    The seven-segment displays are divided into 2 groups (see _Fig. 1_):

    -   `PC` — displays the lower 16 bits of the program counter as a hexadecimal number, derived from the `instr_addr_o` output of the processor core module.
    -   `operation` — displays the [operation](#Operations-displayed-by-the-prototype) currently being executed by the processor.

## Operations displayed by the prototype

The prototype determines the operation type from the lower 7 bits of the instruction.

If the operation type is legal within the processor implemented in the lab assignments, the corresponding opcode is displayed. Opcodes are defined in [decoder_pkg.sv](../../05.%20Main%20decoder/decoder_pkg.sv). If the operation type determined by the prototype is illegal, the seven-segment displays show `ILL` (from **ill**egal).

The mapping between operations and their representation on the seven-segment displays is shown in _Fig. 2_:

!['../../../.pic/Labs/board%20files/nexys_processor_system_operations.drawio.svg'](../../../.pic/Labs/board%20files/nexys_processor_system_operations.drawio.svg)

_Figure 2. Mapping between operations and their representation on the seven-segment displays._

## Demo program

The recommended demo program is [program.mem](../program.mem). A description of its operation can be found in the [#task](../#Task) section.
