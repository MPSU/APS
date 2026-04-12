# FPGA Implementation Steps

In order to implement a device described in a **hardware description language** on an FPGA, several steps must be completed:

1. Elaboration
2. Synthesis
3. Implementation
4. Bitstream generation

The boundary between steps is quite conditional, and depending on the **electronic design automation** (**EDA**) tool used, the tasks performed at different steps may overlap. The description of the steps will be given for the FPGA design flow; however, with some caveats, the same steps are used in ASIC design as well.

Let us examine each step in detail.

## Elaboration

During the elaboration step, the EDA tool parses and analyzes the HDL description of your device, checks it for syntax errors, substitutes parameter values, expands constructs used for repetitive or parameterizable parts of the code, resolves signal widths, and builds the module hierarchy of the device.

It then maps individual sections of code to the corresponding abstract elements: logic gates, multiplexers, memory elements, and so on. Additionally, the circuit is analyzed and optimized — for example, if some part of the logic is ultimately not connected to any output signal, it will be removed[[1]](https://support.xilinx.com/s/question/0D52E00006iHshoSAC/what-exactly-is-elaborating-a-design?language=en_US).

The result of elaboration is the so-called **netlist**. A **netlist** is a representation of a digital circuit as a **graph**, where each circuit element is a node of the graph, and the **nets** connecting these elements are its edges. A netlist can be stored either as internal EDA tool files (as is the case for the elaboration netlist) or as an **HDL** file describing primitive instances and the connections between them. Let us examine the elaboration step and the concept of a netlist using an example.

Suppose we want to implement the circuit shown in _Figure 1_.

![../.pic/Introduction/Implementation%20steps/fig_01.drawio.svg](../.pic/Introduction/Implementation%20steps/fig_01.drawio.svg)

_Figure 1. Example of a simple digital circuit._

It can be described with the following **SystemVerilog** code:

```SystemVerilog
module sample(
  input  logic a, b, c, d, sel,
  output logic res
);

logic ab, xabc;

assign ab = a & b;
assign xabc = ab ^ c;
assign res = sel? d : xabc;

endmodule
```

Let us perform the elaboration step. To do this, in **Vivado**, under the `RTL Analysis` tab, select `Schematic`.

The following windows will open:

![../.pic/Introduction/Implementation%20steps/fig_02.png](../.pic/Introduction/Implementation%20steps/fig_02.png)

_Figure 2. Result of the elaboration step._

In the left window we can see our netlist. The lower section shows the graph nodes (elements **ab_i**, **res_i**, **xabc_i**, which represent **AND**, a **multiplexer**, and **XOR** respectively; the names of these elements correspond to the names of the wires whose assignments created them).

The upper section shows the **graph edges** connecting the circuit elements. These are the inputs and outputs of our module, as well as the intermediate nets we created.

On the right, you see the **schematic** — a **graphical diagram** built from this **graph** (**netlist**).

## Synthesis

During the synthesis step, the EDA tool takes the previously generated digital circuit and implements its elements using the primitives of the specific FPGA — primarily through logic cells containing look-up tables, a full 1-bit adder, and a `D flip-flop` (see [how an FPGA works](../Introduction/How%20FPGA%20works.md)).

Since the circuit in the example is purely **combinational**, its behavior can be calculated and expressed as a **truth table**, meaning **Look-Up Tables** (**LUTs**) are the best fit for its implementation. Moreover, the `xc7a100tcsg324-1` FPGA contains five-input LUTs, and our circuit has exactly that many inputs. This means the entire circuit's behavior can be replaced by **a single look-up table** inside the FPGA.

Let us continue with our example and perform the synthesis step. To do this, click the `Run Synthesis` button.

After synthesis completes, we will be able to open the new schematic shown in Figure 3.

![../.pic/Introduction/Implementation%20steps/fig_03.png](../.pic/Introduction/Implementation%20steps/fig_03.png)

_Figure 3. Result of the synthesis step._

We can see that new primitives — **buffers** — have appeared between the circuit's inputs/outputs and its internal logic. These are needed to convert voltage levels between the FPGA pins and its internal logic (loosely speaking, signals arriving at FPGA inputs may have a level of `3.3 V`, while the primitives inside the FPGA operate with signals at `1.2 V`).

The logic itself, as we expected, has been folded into a single five-input look-up table.

The line `EQN=32'hAAAA3CCC` means that the look-up table will be initialized with the following 32-bit value: `0xAAAA3CCC`.
Since the circuit has 5 inputs, there are 2<sup>5</sup>=32 possible input signal combinations, and each one requires its own result value.

Is it possible to verify this 32-bit value without computing all 32 combinations by hand?
<details>
<summary>
Yes, it is.
</summary>
First, we need to understand the exact order in which these combinations appear. We can see that the signals are connected to the look-up table in the following order: `d, c, b, a, sel`. This means the table takes the following form:

```ascii
|sel| a | b | c | d |  |res|
|---|---|---|---|---|  |---|
| 0 | 0 | 0 | 0 | 0 |  | 0 |
| 0 | 0 | 0 | 0 | 1 |  | 0 |
| 0 | 0 | 0 | 1 | 0 |  | 1 |
| 0 | 0 | 0 | 1 | 1 |  | 1 |
| 0 | 0 | 1 | 0 | 0 |  | 0 |
....
| 1 | 1 | 1 | 1 | 1 |  | 1 |
```

Let us look at the logic of the original circuit and this truth table: when `sel==1`, the output is `d`, which means we already know all values for the lower half of the truth table. In the lower half, the leftmost input signal (`sel`) is always `1`, so the result will match signal `d`, which continuously alternates between `0` and `1` and ends with `1`. This means that reading the result values from bottom to top (from most significant to least significant), we first have 16 digits representing 8 pairs of `10`: `101010101010`, which is equivalent to `AAAA` in hexadecimal.

Computing the remaining 16 cases is also unnecessary. Looking at the circuit, we can notice that when `sel!=1`, neither `sel` nor `d` play any role in controlling the output. The output depends on the XOR operation, which produces `1` only when its inputs differ. The upper XOR input (the AND output) equals one only when both `a` and `b` are one, and at this point we are only interested in cases where `sel!=1`. Given that the truth table lists input values in alternating powers of two (ones, pairs, fours, eights), we understand that the portion of the truth table we are interested in looks as follows:

```ascii
       ...

  | a | b | c |
. |---|---|---| .
. | 1 | 1 | 0 | .
. | 1 | 1 | 0 | .
  | 1 | 1 | 1 |
  | 1 | 1 | 1 |

       ...
```

Only in this part of the truth table do we get `1` at the AND output, and in the upper part of this section, input `c` is also `1`. This means the XOR inputs are equal and the output is `0`. Therefore, the result for this portion of the truth table is `0011`, or `3` in hexadecimal.

Below this section of the truth table is the part where `sel==1`, and above it is the part where the AND output equals `0`. This means the remaining lower portion will repeat the values of `c`, which alternates in pairs of zeros and ones: `00-11-00-11..`. This remaining sequence is written in hexadecimal as `0xCCC`.

Thus, we arrive at the expression `EQN=32'hAAAA3CCC`. If this section was difficult to follow, try constructing the full truth table (without computing the actual results), and then review the logic for the fast result derivation.
</details>

## Implementation

After obtaining the netlist in which the elements are the primitives of the specific FPGA, the circuit is **placed** onto the FPGA's logic elements: specific logic cells are selected. Then **routing** of the connections between them is performed. These procedures are commonly referred to as **place & route**. For example, implementing a 32-bit carry-lookahead adder may require 32 LUTs and 8 fast carry computation primitives (`CARRY4`). It would be inefficient to use primitives scattered across the entire FPGA die, as this would require complex signal routing and would degrade the timing characteristics of the device (signals travelling from one bit to the next would have to traverse longer paths). Instead, the EDA tool attempts to place the circuit such that nearby FPGA primitives are used, in order to achieve optimal characteristics.

What exactly is considered "optimal" depends on two things: the EDA tool settings and the **constraints** applied when building the final circuit on the FPGA. Constraints narrow the solution space for primitive placement inside the FPGA to meet specific characteristics (timing and physical). For example, you can specify that the circuit must be placed such that the **critical path** delay does not exceed `20 ns`. This is a timing constraint. You also need to tell the EDA tool which FPGA pin the inputs and outputs of your circuit should be connected to — this is a physical constraint.

Constraints are not described in a hardware description language; instead, plain text files in a special format specific to the EDA tool are used.

<details>
<summary>
Example constraints used for the ALU lab targeting the <code>Nexys A7-100T</code> development board (higher-order switch and LED bits are omitted for clarity, as the constraints for each bit are identical).
</summary>

Lines beginning with `#` are comments.

Lines beginning with `set_property` are physical constraints that bind the inputs and outputs of our circuit to specific FPGA pins.

The `create_clock...` line defines timing constraints, specifying the target clock frequency and its [duty cycle](https://ru.wikipedia.org/wiki/%D0%A1%D0%BA%D0%B2%D0%B0%D0%B6%D0%BD%D0%BE%D1%81%D1%82%D1%8C).

```xdc
## This file is a general .xdc for the Nexys A7-100T

# Clock signal

set_property -dict { PACKAGE_PIN E3    IOSTANDARD LVCMOS33 } [get_ports { CLK100 }]; #IO_L12P_T1_MRCC_35 Sch=clk100mhz
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports {CLK100}];

# Switches
set_property -dict { PACKAGE_PIN J15   IOSTANDARD LVCMOS33 } [get_ports { SW[0] }]; #IO_L24N_T3_RS0_15 Sch=sw[0]
set_property -dict { PACKAGE_PIN L16   IOSTANDARD LVCMOS33 } [get_ports { SW[1] }]; #IO_L3N_T0_DQS_EMCCLK_14 Sch=sw[1]
# ...

### LEDs

set_property -dict { PACKAGE_PIN H17   IOSTANDARD LVCMOS33 } [get_ports { LED[0] }]; #IO_L18P_T2_A24_15 Sch=led[0]
set_property -dict { PACKAGE_PIN K15   IOSTANDARD LVCMOS33 } [get_ports { LED[1] }]; #IO_L24P_T3_RS1_15 Sch=led[1]
# ...

## 7 segment display
set_property -dict { PACKAGE_PIN T10   IOSTANDARD LVCMOS33 } [get_ports { CA }]; #IO_L24N_T3_A00_D16_14 Sch=ca
set_property -dict { PACKAGE_PIN R10   IOSTANDARD LVCMOS33 } [get_ports { CB }]; #IO_25_14 Sch=cb
# ...

# set_property -dict { PACKAGE_PIN H15   IOSTANDARD LVCMOS33 } [get_ports { DP }]; #IO_L19N_T3_A21_VREF_15 Sch=dp
set_property -dict { PACKAGE_PIN J17   IOSTANDARD LVCMOS33 } [get_ports { AN[0] }]; #IO_L23P_T3_FOE_B_15 Sch=an[0]
set_property -dict { PACKAGE_PIN J18   IOSTANDARD LVCMOS33 } [get_ports { AN[1] }]; #IO_L23N_T3_FWE_B_15 Sch=an[1]
# ...

## Buttons
set_property -dict { PACKAGE_PIN C12   IOSTANDARD LVCMOS33 } [get_ports { resetn }]; #IO_L3P_T0_DQS_AD1P_15 Sch=cpu_resetn
```

</details>

After implementation completes, the netlist and the digital circuit itself remain unchanged; however, the primitives used to realize the circuit are assigned their "address" inside the FPGA:

![cell_add../.pic/Introduction/Implementation%20steps/fig_04.png](../.pic/Introduction/Implementation%20steps/fig_04.png)

_Figure 4. The "address" of a specific LUT inside the FPGA._

Now we can look at the "internals" of our FPGA `xc7a100tcsg324-1` and see how our circuit is implemented through its primitives. To do this, open the implemented design: `Implementation -> Open implemented design`. The window shown in _Fig. 5_ will open.

![../.pic/Introduction/Implementation%20steps/fig_05.png](../.pic/Introduction/Implementation%20steps/fig_05.png)

_Figure 5. The implemented design viewer window._

This is the contents of the FPGA. Due to the enormous number of primitives it contains, it is displayed at a scale where everything blends into a single colored mosaic. Most of this window is inactive (shown in dark blue tones), and that is expected — we implemented a tiny digital circuit that should not occupy a significant amount of FPGA resources.

We are interested in the "[pale blue dot](https://en.wikipedia.org/wiki/Pale_Blue_Dot)" located in the lower-left corner of the rectangle `X0Y1` (highlighted in red). Zooming into that area, we will find the LUT we are using:

![../.pic/Introduction/Implementation%20steps/fig_06.png](../.pic/Introduction/Implementation%20steps/fig_06.png)

_Figure 6. Location of the selected LUT inside the FPGA._

Furthermore, by examining the properties of this primitive, we can find the truth table used to initialize it.

## Bitstream generation

After the EDA tool has determined the specific primitives, their operating modes, and the signal paths between them, a binary file (**bitstream**) must be generated. This file will configure the FPGA in the required way.
Once this file is obtained, all that remains is to program the FPGA, after which it will implement the designed device.

## Chapter Summary

The flow from an HDL description of a device to its implementation on an FPGA is as follows:

1. First, the **elaboration** step takes place. Its main tasks include:
   1. flattening the module hierarchy: converting the hierarchical project structure into a flat one, which simplifies subsequent processing steps;
   2. syntax and semantic checking of the HDL code;
   3. resolving parameters and constants;
   4. generating an intermediate project representation used in subsequent steps.
   The resulting intermediate representation uses abstract elements (logic gates, multiplexers, registers) that are not tied to any specific FPGA.
2. Next, the **synthesis** step is performed, producing a **netlist** that uses the resources of the specific FPGA. All structures used in the previous step (registers, multiplexers, and other blocks) are implemented through FPGA primitives (LUTs, D flip-flops, arithmetic blocks, etc.). A logic network optimization step is performed to minimize area, reduce delays, and lower power consumption.
3. Then the **implementation** step builds the final digital circuit, consisting of several sub-steps:
   1. **Placement**: determining the specific locations of all logic elements within the FPGA. If part of the circuit was implemented using LUTs in the previous step, this step decides **which specific** LUT will be used (not its type, but which of the many identical elements will be selected).
   2. **Routing**: creating connections between elements in accordance with the netlist.
   3. **Timing Analysis**: verifying timing characteristics to confirm that all signals propagate through the circuit within acceptable timing margins.
   The solution space for the **place & route** steps is constrained by applying **physical** and **timing** **constraints**.
4. The final step is **bitstream generation**, which produces the binary configuration file that will configure the FPGA to implement the built circuit when programmed.

## References

1. [Xilinx Forum: what exactly is 'elaborating' a design?](https://support.xilinx.com/s/question/0D52E00006iHshoSAC/what-exactly-is-elaborating-a-design?language=en_US)
