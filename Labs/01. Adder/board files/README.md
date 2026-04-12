# Testing the Full 32-bit Adder on FPGA

After creating and verifying the 32-bit adder in simulation, you need to test it on an FPGA prototype.

Instructions for implementing the prototype are described [here](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

_Fig. 1_ shows the prototype schematic on the FPGA.

![../../../.pic/Labs/board%20files/nexys_adder_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_adder_structure.drawio.svg)

_Figure 1. Block diagram of the `nexys_adder` module._

The `nexys_adder` module allows you to supply data from the switches <span style="color:#FF6666;">❶</span> to the `a_i` and `b_i` inputs, and also to pass the carry-in bit using button <span style="color:#FF6666;">❷</span> `BTND` to the `carry_i` input.

The switches are split evenly between operands `a_i` and `b_i` (switches `sw[7:0]` correspond to operand `b_i`, switches `sw[15:8]` correspond to operand `a_i`). Since there are only 16 switches in total, each operand gets 8. Thus, only the 8 least significant bits of each operand can be entered via the switches.

The upper bits are padded with zeros, which means the prototype can add numbers in the range `[0:255]` (plus the carry-in bit), giving a result range of `[0:511]`.

The seven-segment displays <span style="color:#FF6666;">❸</span> show the values of operands `a_i` and `b_i` in hexadecimal on the left block, and the sum result on the right block. The LEDs <span style="color:#FF6666;">❹</span> above the switches duplicate the sum in binary format.

_Fig. 2_ shows an example of adding `0x48 + 0x18 = 0x60` with zero carry-in (zero because the `BTND` button is not pressed).

![../../../.pic/Labs/board%20files/nexys_adder_48_plus_18.drawio.svg](../../../.pic/Labs/board%20files/nexys_adder_48_plus_18.drawio.svg)

_Figure 2. Using the adder to compute `0x48 + 0x18` on the FPGA._
