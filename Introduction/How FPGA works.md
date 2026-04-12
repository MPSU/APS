# What is an FPGA and How Does It Work

- [What is an FPGA and How Does It Work](#what-is-an-fpga-and-how-does-it-work)
  - [History of FPGAs](#history-of-fpgas)
  - [Digital Circuits and Logic Gates](#digital-circuits-and-logic-gates)
    - [Digital Circuits](#digital-circuits)
    - [Logic Gates](#logic-gates)
    - [Multiplexers](#multiplexers)
    - [Programmable Memory](#programmable-memory)
  - [Look-Up Tables (LUTs)](#look-up-tables-luts)
  - [D Flip-Flops](#d-flip-flops)
  - [Arithmetic](#arithmetic)
  - [Logic Blocks](#logic-blocks)
  - [Interconnect Network](#interconnect-network)
  - [Chapter Summary](#chapter-summary)
  - [References](#references)

> The sections "Digital Circuits and Logic Gates" and "Look-Up Tables" draw heavily from the article "[How Does an FPGA Work?[1]](https://learn.sparkfun.com/tutorials/how-does-an-fpga-work/all)" by `Alchitry, Ell C`, distributed under the [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/) license.

## History of FPGAs

Before integrated circuits existed, electronic devices were built using vacuum tubes, which performed amplification and switching functions. These tubes were bulky, power-hungry, and short-lived. They were later replaced by transistors, which became the foundation of modern electronic circuits. Initially, transistors were used as discrete components just like tubes, and circuits were assembled from them like a Lego model. If a mistake was made, it could be corrected by manually reworking the connections between components, much like fixing an error when building a Lego model.

As technology advanced, transistors were miniaturized, making it possible to place them together with their interconnections on a single die. This gave rise to integrated circuits — electronic circuits fabricated on a semiconductor substrate and enclosed in a sealed package. This transition was a revolutionary step in the development of electronics, paving the way for compact and high-performance devices.

In most cases, it is impossible to correct a mistake made during the design and manufacture of an integrated circuit. Given that fabricating a prototype integrated circuit is a lengthy and expensive process (costing tens of thousands to millions of dollars), there arose a need for a flexible, fast, and inexpensive way to prototype and verify a circuit before committing to fabrication. This is how **programmable logic devices** (**PLDs**) came about.
It should be noted that this book mainly focuses on a specific type of PLD known as an FPGA (field-programmable gate array).

An FPGA contains a finite set of basic building blocks (primitives), primitive interconnect blocks, and input/output blocks. By applying a specific set of configuration data to an FPGA (**programming** it), the primitives, their interconnections with each other, and with the I/O blocks can be configured to implement a desired digital circuit. The advantage of an FPGA is that if an error is found in a prototype implemented on the FPGA, the digital circuit can be corrected and the FPGA reprogrammed.

In addition, FPGAs can be used effectively not only as a low-cost prototyping tool, but also as the final implementation vehicle for low-volume products (it is cheaper to buy and program an off-the-shelf batch of FPGAs than to fabricate a custom batch of chips).

Let us take a closer look at what this device is and how it works internally, but first we need to cover some basics of digital circuits and logic gates.

## Digital Circuits and Logic Gates

### Digital Circuits

A **digital circuit** is an **abstract model** of computation that operates on two discrete states, commonly denoted as `0` and `1`. It is important to understand that these states are not tied to specific physical quantities such as voltage in an electrical circuit. Instead, they represent generalized logical values that can be implemented on any technology capable of distinguishing two discrete states.

Thanks to this abstraction, digital circuits can be implemented not only using traditional electronic components, but also on entirely different platforms — for example, using [pneumatic systems](https://habr.com/ru/companies/ruvds/articles/692236/), [cardboard and marbles](https://habr.com/ru/articles/399391/), [redstone dust](https://minecraft.fandom.com/wiki/Tutorials/Redstone_computers) in Minecraft, or even through human interaction, as described in Liu Cixin's novel "The Three-Body Problem" (the efficiency of such implementations is another matter entirely). The core idea is that a digital circuit is decoupled from its physical implementation, focusing solely on the logic of interactions between the states `0` and `1`, which makes it universal and technology-independent.

Of course, when designing efficient digital circuits, the underlying technology must be taken into account.

In electronics, the word "digital" describes circuits that abstract away from continuous (analog) voltage values, using only two discrete values: `0` and `1`. At this level of abstraction, we are not concerned with specific voltage levels or their thresholds, which allows us to design circuits in an idealized world where voltage can have only two values: `0` and `1`. Ensuring these conditions is the responsibility of the basic building blocks from which digital circuits are constructed.

These basic building blocks are called **logic gates**.

### Logic Gates

There are many types of logic gates; we will consider four of them: **AND**, **OR**, **XOR**, and **NOT**. Each of these elements accepts a **digital value** as input (see [**Digital Circuits**](#digital-circuits)), performs a specific **logical function** on its inputs, and produces the result of that function as a **digital value** on its output.

The logic gates in _Figs. 1–4_ are illustrated using standard schematic symbols from two standards: **ANSI** and **GOST**. Since the ANSI variant is widely used in the literature, it will be used throughout this book.

The **AND** gate takes two inputs and outputs a value of `1` only when both inputs are `1`. If at least one input is `0`, the output is `0`. The **AND** gate is represented on schematics as follows:

![../.pic/Introduction/How%20FPGA%20works/fig_01.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_01.drawio.svg)

_Figure 1. Schematic symbol of the **AND** gate._

The **OR** gate takes two inputs and outputs a value of `1` if at least one input equals `1`. If both inputs are `0`, the output is `0`. The **OR** gate is represented on schematics as follows:

![../.pic/Introduction/How%20FPGA%20works/fig_02.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_02.drawio.svg)

_Figure 2. Schematic symbol of the **OR** gate._

The **XOR** (Exclusive OR) gate takes two inputs and outputs a value of `1` when the input values are not equal to each other (one is `1` and the other is `0`). If both inputs are equal (both `0` or both `1`), the output is `0`. The **XOR** gate is represented on schematics as follows:

![../.pic/Introduction/How%20FPGA%20works/fig_03.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_03.drawio.svg)

_Figure 3. Schematic symbol of the **XOR** gate._

The **NOT** gate is the simplest. It takes a single input and outputs its inverse. If the input is `0`, the output is `1`; if the input is `1`, the output is `0`. It is represented on schematics as follows:

![../.pic/Introduction/How%20FPGA%20works/fig_04.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_04.drawio.svg)

_Figure 4. Schematic symbol of the **NOT** gate._

There are also variations of the basic gates, such as **NAND**, **NOR**, and **XNOR**, which differ from their base counterparts in that the result of the operation is inverted relative to the result of the corresponding operation without the inversion.

Logic gates can be built from **transistors**. A **transistor** is a device that can pass or block current depending on the voltage applied to its control terminal.

A key feature of modern integrated circuits is that they are built using complementary (**P**- and **N**-type) transistor pairs — **Complementary Metal-Oxide-Semiconductor** (**CMOS**) logic. For this type of transistor, it turns out to be more efficient to implement **NAND** and **NOR** operations.

From the perspective of building digital circuits, MOS transistors (**P**- and **N**-type) can be thought of as switches that either connect or disconnect two terminals. The difference between **P**- and **N**-type transistors lies in the voltage at the control terminal that causes the transistor to be "on" (terminals connected) or "off" (connection broken). _Fig. 5_ illustrates this difference.

The terminals between which the connection is formed are called the "**drain**" (**d**) and "**source**" (**s**), and the control terminal is called the "**gate**" (**g**). Note that a **logic gate** and a transistor **gate** are different things!

![../.pic/Introduction/How%20FPGA%20works/fig_05.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_05.drawio.svg)

_Figure 5. P-type and N-type MOS transistors._

_Fig. 6_ shows how **NAND** and **NOR** gates are constructed using **CMOS** technology. Let us walk through the operation of the **NAND** gate.

Applying a value of `1` to input **A** or **B** turns on the corresponding N-channel transistor (shown in red in _Fig. 6_) and turns off its complementary P-channel transistor (shown in blue). Applying `1` to both inputs turns off both P-channel transistors (the upper portion of the circuit is open, effectively removing it from the output) and turns on both N-channel transistors. As a result, the output is connected to "ground" (the black triangle at the bottom of the circuit), which is equivalent to `0` in terms of digital values.

If at least one of the inputs **A** or **B** is `0`, one of the parallel-connected P-channel transistors turns on (while the connection to "ground" is broken), and the output is connected to the supply voltage (the two perpendicular lines at the top of the circuit), which is equivalent to `1` in terms of digital values.

As you can see, the output voltage is driven from the **power supply** or **ground**, not from the gate inputs themselves. This is precisely what ensures continuous voltage refresh and noise immunity of **digital circuits**.

![../.pic/Introduction/How%20FPGA%20works/fig_06.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_06.drawio.svg)

_Figure 6. Schematic of **NAND** and **NOR** gates built from CMOS transistors._

As a rule, when it is necessary to invert an input or output of a logic element in a schematic, a small circle is drawn on it rather than adding an explicit **NOT** gate as shown in _Fig. 4_. For example, the **NAND** gate is represented in the form shown in _Fig. 6_.

If desired, a **NAND** gate can easily be converted into an **AND** gate (just as a **NOR** gate can be converted into an **OR** gate) by placing an inverter at the output of **NAND**, built from two MOS transistors as shown in _Fig. 7_.

![../.pic/Introduction/How%20FPGA%20works/fig_07.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_07.drawio.svg)

_Figure 7. Schematic of a **NOT** gate built from CMOS transistors._

CMOS logic is far from the only way to build digital elements; other approaches were widely used in the past, such as circuits built using only one type of transistor. However, the use of complementary pairs has proven to be the most efficient, and today this approach dominates digital circuit design.

Using only the logic gates described above, it is possible to build **any(!)** digital circuit.

However, when describing digital circuits, certain digital blocks are used so frequently that dedicated symbols have been introduced for them — **adders**, **multipliers**, **multiplexers**, etc. — which are used when describing more complex circuits. Let us look at one of the fundamental building blocks in an FPGA: the **multiplexer**.

### Multiplexers

A multiplexer is a device that routes one of its input signals to the output, depending on the value of a **select signal**.

The schematic symbol of a multiplexer is shown in _Figure 8_.

![../.pic/Introduction/How%20FPGA%20works/fig_08.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_08.drawio.svg)

_Figure 8. Multiplexer symbol._

The `/` symbol on the `sel` line indicates that this signal is multi-bit, and the number below specifies that the signal width is 6 bits.

A multiplexer can have any number of inputs, but always has exactly one output.

**The way in which the select signal is encoded can also vary.** The simplest digital multiplexer circuit results from using [**one-hot**](https://en.wikipedia.org/wiki/One-hot) encoding. With this encoding, the value of the **multi-bit** select signal **always** contains **exactly one** `1`. The information carried by such an encoded signal is contained in the position of that `1` within the select signal.

Let us see how a multiplexer with a one-hot-encoded select signal can be implemented using only **AND** and **OR** gates:

![../.pic/Introduction/How%20FPGA%20works/fig_09.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_09.drawio.svg)

_Figure 9. Multiplexer implementation using one-hot encoding._

If we set the select signal to `000010`, meaning that only the **first** bit of this signal (**counting from zero**) equals **one** (`sel[1] = 1`), we can see that a value of `0` is applied to one input of each **AND** gate. The exception is the **AND** gate for input `b`, which receives a value of `1`. This means that all **AND** gates (except the one connected to input `b`) will output `0` (see [Logic Gates](#logic-gates)) regardless of what is applied to inputs a, c, d, e, and f. The only input that will affect the circuit's output is `b`. When it is `1`, the corresponding **AND** gate outputs `1`. When it is `0`, the **AND** gate outputs `0`. In other words, the **AND** gate's output mirrors the value of `b`.

![../.pic/Introduction/How%20FPGA%20works/fig_10.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_10.drawio.svg)

_Figure 10. Multiplexer implementation using one-hot encoding._

The **OR** gate in this circuit has more than two inputs. Such a gate can be constructed as a cascade of two-input **OR** gates:

![../.pic/Introduction/How%20FPGA%20works/fig_11.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_11.drawio.svg)

_Figure 11. Multi-input **OR** gate implementation._

A **multi-input OR gate** behaves exactly like a two-input one: it outputs `1` when at least one input is `1`. If all inputs are `0`, the output is `0`.

In our multiplexer circuit, it is guaranteed that every input of the **OR** gate except one will be `0` (since every **AND** gate output except one will be `0`). This means the output of the **multi-input OR** gate depends on only **one** input (when `sel = 000010`, it depends on input `b`).

![../.pic/Introduction/How%20FPGA%20works/fig_12.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_12.drawio.svg)

_Figure 12. Multiplexer implementation using one-hot encoding._

By changing the value of `sel`, we can control which multiplexer input is routed to the output.

### Programmable Memory

Transistors can be used to build not only logic elements, but also memory elements. Fig. 13 shows a schematic of the simplest static memory cell, consisting of one transistor and two inverters (totaling 5 transistors, which is why it is called **5T** SRAM). This cell implements 1 bit of programmable memory and was one of the core components of the very first FPGA.

![../.pic/Introduction/Sequential%20logic/fig_06.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_06.drawio.svg)

_Figure 13. Programmable memory cell of the Xilinx XC2064 FPGA [[2, p. 2-63](https://archive.org/details/programmablegate00xili/page/n93/mode/2up)]._

This memory is a **bistable cell** — a loop of two inverters in which the stored value is "latched". A signal inverted twice returns to its original value, and as it passes through each inverter, the signal's voltage level is refreshed, preventing it from decaying due to circuit resistance.

To write a new value into the bistable cell, an additional transistor is connected to its input, which connects or disconnects it from the supply voltage or ground.

## Look-Up Tables (LUTs)

Imagine a multiplexer with four input signals and a two-bit select signal (note that this signal now uses standard binary encoding). But instead of exposing the input signals to the outside world, let us connect them to programmable memory. This means we can "program" each input to hold a constant value. If we enclose the result in a separate block, we obtain a two-input **Look-Up Table** (**LUT**).

![../.pic/Introduction/How%20FPGA%20works/fig_14.drawio.svg](../.pic/Introduction/How%20FPGA%20works/fig_14.drawio.svg)

_Figure 14. Look-Up Table (LUT) implementation._

The two inputs of the **LUT** are the bits of the select signal of the multiplexer hidden inside the **LUT**. By programming the multiplexer inputs (more precisely, by programming the memory to which the multiplexer inputs are connected), we can implement **any(!)** logical function with two inputs and one output on top of the **LUT**.

For example, suppose we want to implement **logical AND**. To do so, we need to write the following content into the memory:

| Address ({x, y}) | Value (f) |
|------------------|-----------|
|        00        |     0     |
|        01        |     0     |
|        10        |     0     |
|        11        |     1     |

This is the simplest example — in practice, **LUT**s typically have more inputs, allowing them to implement more complex logic.

## D Flip-Flops

As you have already seen, using an unlimited number of LUTs, you can build a digital circuit that implements a logical function of any complexity. However, digital circuits are not limited to implementing logical functions only (circuits that implement logical functions are called **combinational circuits**, because the output depends only on the current combination of inputs). For example, a digital circuit implementing a processor cannot be built this way. Such circuits require memory elements. Note that we are not talking about the programmable memory used to configure the logic functions implemented by the LUTs — we are talking about memory cells used by the circuit's own logic.

The fundamental memory element is the **D flip-flop**. D flip-flops can be used to build other memory elements, such as **registers** (and registers can be used to build **random access memory** (**RAM**)), **shift registers**, and so on.

A **D flip-flop** is a digital element capable of storing one bit of information. In its basic form, it has two inputs and one output. One input receives the value to be stored in the **D flip-flop**; the other controls the write operation (typically called `clk` or `clock`, and connected to the circuit's clock signal). When the control signal transitions from `0` to `1` (or from `1` to `0`, depending on the design), the data signal's value is captured into the **D flip-flop**. It is commonly said that a **D flip-flop** is built from two **D latches**, which in turn are built from **SR latches**. Ultimately, however, all of these elements can be implemented using **AND**/**OR** and **NOT** gates:

![../.pic/Introduction/Sequential%20logic/fig_05.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_05.drawio.svg)

_Figure 15. D flip-flop implementation._

## Arithmetic

In addition to the blocks described above (multiplexers and the LUTs and registers built on top of them), there is another type of block so frequently used in digital circuits that it is pre-placed in FPGAs in large quantities: **arithmetic blocks**. These blocks are used for addition, subtraction, comparison, and counter implementations. Different FPGAs may include different arithmetic primitives: some include a 1-bit adder, others a carry-chain block.

All of these blocks can be implemented using logic gates. For example, here is how a full adder can be implemented:

![../.pic/Labs/lab_01_adder/fig_02.drawio.svg](../.pic/Labs/lab_01_adder/fig_02.drawio.svg)

_Figure 16. Full 1-bit adder implementation._

## Logic Blocks

The previous sections covered individual types of digital blocks: look-up tables, registers, and arithmetic blocks. For structural convenience, these blocks are grouped together inside an FPGA as **logic blocks**. Typically, logic blocks in modern FPGAs consist of **logic cells** (or **logic elements**), but for simplicity we will use these terms interchangeably.

A logic block can contain one or more **LUT**s, an **arithmetic block**, and one or more **D flip-flops**, connected to each other through a number of multiplexers. _Figure 17_ shows what a logic block may look like:

![../.pic/Labs/lab_03_memory/fig_02.png](../.pic/Labs/lab_03_memory/fig_02.png)

_Figure 17. Logic cell schematic [[2]](https://en.wikipedia.org/wiki/Field-programmable_gate_array)._

A logic block represents a chain of operations: `logical function implemented in LUT → arithmetic operation → write to D flip-flop`. Each multiplexer determines whether any of these stages is bypassed.
By configuring a logic block, the following variations of a circuit fragment can be obtained:

1. Combinational circuit (logical function implemented in a LUT)
2. Arithmetic operation
3. Write data to a D flip-flop
4. Combinational circuit with the result written to a D flip-flop
5. Arithmetic operation with the result written to a D flip-flop
6. Combinational circuit followed by an arithmetic operation
7. Combinational circuit followed by an arithmetic operation and a write to a D flip-flop

_Figure 18_ shows a real example of logic block usage in the `xc7a100tcsg324-1` FPGA when implementing an Arithmetic Logic Unit (ALU) connected to the peripherals of the `Nexys-7` development board. In this figure, you can see the use of LUTs, an arithmetic block (carry-lookahead), and one of the D flip-flops. D flip-flops shown in grey are unused.

![../.pic/Introduction/How%20FPGA%20works/fig_18.png](../.pic/Introduction/How%20FPGA%20works/fig_18.png)

_Figure 18. Example of logic cell usage._

With a large set of such logic blocks and the ability to interconnect them as needed, you have extensive capabilities for implementing virtually any digital circuit (the only limitation is the FPGA's capacity — i.e., the number of logic blocks, I/O pins, and so on).

In addition to logic blocks, FPGAs also include other primitives: **block RAM**, **multiplier blocks**, and so on.

## Interconnect Network

To understand how the interconnection of logic blocks is controlled, let us look at Fig. 19, taken from the FPGA patent [[4](https://patents.google.com/patent/US4870302A)].

![../.pic/Introduction/How%20FPGA%20works/fig_19.jpg](../.pic/Introduction/How%20FPGA%20works/fig_19.jpg)

_Figure 19. FPGA contents showing the interconnection of logic blocks and I/O blocks [[5](http://www.righto.com/2020/09/reverse-engineering-first-fpga-chip.html)]._

Nine logic blocks are shown in blue, and twelve I/O blocks in yellow. All of these blocks are surrounded by an **interconnect network**, which consists of a grid of horizontal and vertical wiring lines — the general purpose interconnect [[2, 2-66](https://archive.org/details/programmablegate00xili/page/n97/mode/2up)].

The diagonal marks at line crossings represent **programmable interconnect points** (**PIPs**): transistors whose gates are connected to programmable memory.

By controlling the value stored in the memory connected to a transistor's gate, it is possible to determine whether that transistor acts as an open connection or a closed switch at that point in the grid. This allows "unused" segments of the network to be removed, leaving only the routes needed to connect the logic blocks to each other.

## Chapter Summary

1. Using elements such as **transistors**, it is possible to build **logic gates**: **AND**, **OR**, **NOT**, and so on.
2. Using **logic gates**, it is possible to create circuits that implement both **logical functions** (**combinational circuits**) and complex logic with memory (**sequential circuits**).
3. Logic gates can also be used to build the important combinational circuit known as the **multiplexer**: a digital block that routes one of its input signals to the output based on the value of a select signal.
4. Furthermore, by connecting the input of a bistable cell (a loop of two inverters) to a transistor, one bit of **programmable memory** can be obtained.
5. By connecting the input signals of a multiplexer to programmable memory, a **Look-Up Table** (**LUT**) is obtained, which can implement simple logical functions. LUTs can replace AND/OR/NOT gates and have the advantage of being dynamically reconfigurable. Logic gates, by contrast, are fixed at fabrication and cannot be changed afterwards.
6. Logic gates can also be used to build the basic memory element — the **D flip-flop** — and the combinational circuit known as the **full 1-bit adder** (or any other commonly used arithmetic block).
7. Combining a LUT, an arithmetic block, and a D flip-flop yields the FPGA structure known as a **logic block**.
8. A logic block (as well as other **primitives**, such as **block RAM** or **multipliers**) represents a set of blocks that are physically pre-placed in the FPGA die; their quantity is fixed by the specific FPGA and cannot be changed.
9. By connecting programmable memory to transistors located at the nodes of the **interconnect network**, the placement of breaks in the network can be controlled, making it possible to leave only the routing paths that carry signals where they are needed (**signal routing**).
10. By **configuring primitives** and **routing signals** between them (see item 4), **virtually any digital circuit** can be implemented (subject to the FPGA's capacity constraints).

## References

1. Alchitry, Ell C / [How Does an FPGA Work?](https://learn.sparkfun.com/tutorials/how-does-an-fpga-work/all)
2. Xilinx / [The Programmable Gate Array Data Book](https://archive.org/details/programmablegate00xili)
3. Wikipedia / [Field-programmable gate array](https://en.wikipedia.org/wiki/Field-programmable_gate_array)
4. Ross H. Freeman / Configurable electrical circuit having configurable logic elements and configurable interconnects / United States Patent
5. Ken Shirriff / [Reverse-engineering the first FPGA chip, the XC2064](http://www.righto.com/2020/09/reverse-engineering-first-fpga-chip.html)
