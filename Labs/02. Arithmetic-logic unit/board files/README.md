# Testing the Arithmetic Logic Unit on FPGA

After verifying the ALU in simulation, you need to test it on an FPGA prototype.

Instructions for implementing the prototype are described [here](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

_Fig. 1_ shows the prototype schematic on the FPGA.

![../../../.pic/Labs/board%20files/nexys_alu_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_alu_structure.drawio.svg)

_Figure 1. Block diagram of the `nexys_alu` module, where `SE` blocks are [sign extenders](https://en.wikipedia.org/wiki/Sign_extension)._

The `nexys_alu` module allows you to supply data to the `a_i`, `b_i`, and `alu_op_i` inputs, and to control the interpretation of the operand/result sign using the switches.

Switches `sw[15:0]` and the signals they set correspond as follows:
-   `sw[15:11]` — operand `a_i`.
-   `sw[10:6]` — operand `b_i`.
-   `sw[5]` — `sign_on` (the purpose of this signal is described further below).
-   `sw[4:0]` — `alu_op_i`.

The `sign_on` signal determines how operands `a_i`, `b_i` and result `result_o` are interpreted (signed/unsigned):
-   If the signal is `1` (switch in the "up" position), the operands and result are interpreted and displayed as **signed** numbers.
-   If the signal is `0` (switch in the "down" position), the operands and result are interpreted and displayed as **unsigned** numbers.

The valid range of operand values is therefore:
-   Signed interpretation: `[-16:15]`
-   Unsigned interpretation: `[0:31]`

Numbers are displayed on the seven-segment displays in **decimal**.

The result block shows the sign and the 3 least significant **digits** (hundreds, tens, ones) of the result, taking into account whether it is interpreted as signed or unsigned. For example, the result of `0 - 1` under signed interpretation will be displayed as `-1` on the seven-segment displays, while under unsigned interpretation it will display as `295` (the 3 least significant digits of `4,294,967,295`).

The LEDs above the switches display 15 bits of the result and the flag. That is, `led[15]` is connected to the `flag_o` signal of the ALU, and `led[14:0]` is connected to `result_o[14:0]`.

_Fig. 2_ shows an example of adding `12 + (-16) = -4`.

![../../../.pic/Labs/board%20files/nexys_alu_12_plus_minus_16.drawio.svg](../../../.pic/Labs/board%20files/nexys_alu_12_plus_minus_16.drawio.svg)

_Figure 2. Using the ALU to compute `12 + (-16)` on the FPGA._

Try setting various operations on the switches (addition, subtraction, shift, and comparison), observe the difference between signed/unsigned operations, verify that everything works correctly, and submit your work.
