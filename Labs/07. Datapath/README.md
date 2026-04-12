# Lab 7. Datapath

The microarchitecture can be divided into two parts: the datapath and the control unit. Data flows through the datapath (from instruction memory, the register file, the ALU, data memory, and multiplexers), while the control unit (in our case — the instruction decoder) receives the current instruction from the datapath and tells it exactly how to execute it, i.e., controls how data passes through the datapath.

## Objective

Describe a **RISC-V** processor in **SystemVerilog** by implementing its datapath using previously developed blocks and connecting the control unit to it. The result of this lab will be a RISC-V processor that, for now, can only interact with data memory using 32-bit words (i.e., WITHOUT byte- and halfword-related instructions: `lh`, `lhu`, `lb`, `lbu`, `sh`, `sb`).

## Workflow

1. Study the microarchitectural implementation of the single-cycle RISC-V processor (without support for byte/halfword load/store instructions)
2. Implement the datapath with the control unit connected to it ([#assignment](#Assignment))
3. Prepare a program for the individual task and load it into instruction memory
4. Compare the processor's behavior in the **Vivado** model against the assembly program simulator

## Processor System Microarchitecture

### processor_core

Let us examine the microarchitecture of the `processor_core` module. The microarchitecture of this module is shown in _Fig. 1_.

```Verilog
module processor_core (
  input  logic        clk_i,
  input  logic        rst_i,

  input  logic        stall_i,
  input  logic [31:0] instr_i,
  input  logic [31:0] mem_rd_i,

  output logic [31:0] instr_addr_o,
  output logic [31:0] mem_addr_o,
  output logic [ 2:0] mem_size_o,
  output logic        mem_req_o,
  output logic        mem_we_o,
  output logic [31:0] mem_wd_o
);

endmodule
```

![../../.pic/Labs/lab_07_dp/fig_01.drawio.svg](../../.pic/Labs/lab_07_dp/fig_01.drawio.svg)

_Figure 1. RISC-V processor core microarchitecture._

The proposed microarchitecture shares a similar structure with the `CYBERcobra` processor from [Lab 4](../04.%20Primitive%20programmable%20device/), with some modifications.

First, the processor's inputs and outputs have changed:

- The instruction memory has been moved outside the processor, so the processor now has the `instr_addr_o` and `instr_i` ports;
- Additionally, the module now has data memory interface signals, as implemented in [Lab 6](../06.%20Main%20memory/):
  - `mem_addr_o` — external memory address;
  - `mem_req_o` — request to access external memory;
  - `mem_size_o` — data size for memory access;
  - `mem_we_o` — write enable signal for external memory;
  - `mem_wd_o` — data to write to external memory;
  - `mem_rd_i` — data read from external memory;
  These signals are used when executing load/store instructions for data memory.
- The processor also has a new `stall_i` input that pauses the program counter update.

Furthermore, this microarchitecture uses five different types of immediate constants (corresponding to specific instruction types).

The `I`, `U`, and `S` immediates are used to compute addresses and values. Therefore, all of these constants must be connected to the ALU. This means multiplexers are now required to select what is fed into the ALU operands.

> [!IMPORTANT]
> Note the `imm_U` constant. Unlike all other constants, it is not sign-extended; instead, 12 zero bits are appended to its right.

The `B` and `J` immediates are used for conditional and unconditional branches (in CYBERcobra, a single `offset` constant was used for this purpose).

The program counter (`PC`) now also updates in a more complex way. Since a new type of unconditional branch (`jalr`) has been added, the program counter can not only be incremented by a constant from the instruction, but can also receive an entirely new value as the sum of a constant and a value from the register file (see the leftmost multiplexer in _Fig. 1_). Note that the least significant bit of this sum must be cleared — this is a requirement of the specification [[1](https://github.com/riscv/riscv-isa-manual/releases/download/20240411/unpriv-isa-asciidoc.pdf), p. 28].

Since accessing external memory takes time, the program counter must be stalled to prevent subsequent instructions from executing before the memory access completes. For this purpose, a `stall_i` control signal has been added to the program counter. The program counter can only update when this signal is zero (in other words, the inverse of this signal serves as the `enable` signal for the `PC` register).

### processor_system

After implementing the processor core, memory must be connected to it. This is done in the `processor_system` module.

```Verilog
module processor_system(
  input  logic        clk_i,
  input  logic        rst_i
);

endmodule
```

![../../.pic/Labs/lab_07_dp/fig_02.drawio.svg](../../.pic/Labs/lab_07_dp/fig_02.drawio.svg)

_Figure 2. Processor system microarchitecture._

Pay attention to the `stall` register (_Figure 2_). This register controls the write enable for the program counter. Since we are using block RAM located directly inside the FPGA, access to it takes 1 clock cycle, which means that when a memory access occurs, the program counter must be "disabled" for exactly 1 clock cycle. If truly "external" memory were used (e.g., DDR3), this register would be replaced by different logic that asserts the `stall_i` input of the core while a memory access is in progress.

## Assignment

1. Implement the RISC-V processor core according to the proposed microarchitecture (`processor_core`).
2. Connect instruction memory and data memory to it in the `processor_system` module.
3. Verify the system using the test program from _Listing 1_.
4. Write your own RISC-V assembly program for the individual task chosen in Lab 4, and verify its execution on your processor system.

Let us write a simple program that uses all instruction types to test our processor. First, let us write the program in assembly:

```assembly
00:  addi  x1,  x0, 0x75С
04:  addi  x2,  x0, 0x8A7
08:  add   x3,  x1, x2
0C:  and   x4,  x1, x2
10:  sub   x5,  x4, x3
14:  mul   x6,  x3, x4    // unsupported instruction
18:  jal   x15, 0x00050   // jump to address 0x68
1C:  jalr  x15, 0x0(x6)
20:  slli  x7,  x5, 31
24:  srai  x8,  x7, 1
28:  srli  x9,  x8, 29
2C:  lui   x10, 0xfadec
30:  addi  x10, x10,-1346
34:  sw    x10, 0x0(x4)
38:  sh    x10, 0x6(x4)
3C:  sb    x10, 0xb(x4)
40:  lw    x11, 0x0(x4)
44:  lh    x12, 0x0(x4)
48:  lb    x13, 0x0(x4)
4С:  lhu   x14, 0x0(x4)
50:  lbu   x15, 0x0(x4)
54:  auipc x16, 0x00004
58:  bne   x3,  x4, 0x08  // skip over
5С:                       // the illegal zero instruction
60:  jal   x17, 0x00004
64:  jalr  x14, 0x0(x17)
68:  jalr  x18, 0x4(x15)
```

_Listing 1. Example assembly program._

Now, following the instruction encoding, let us convert the program to machine code:

```text
00:  011101011100  00000 000 00001 0010011 (0x75C00093)
04:  100010100111  00000 000 00010 0010011 (0x8A700113)
08:  0000000 00010 00001 000 00011 0110011 (0x002081B3)
0C:  0000000 00010 00001 111 00100 0110011 (0x0020F233)
10:  0100000 00011 00100 000 00101 0110011 (0x403202B3)
14:  0000001 00100 00011 000 00110 0110011 (0x02418333)
18:  00000101000000000000    01111 1101111 (0x050007EF)
1C:  000000000000  00110 000 01111 1100111 (0x000307E7)
20:  0000000 11111 00101 001 00111 0010011 (0x01F29393)
24:  0100000 00001 00111 101 01000 0010011 (0x4013D413)
28:  0000000 11101 01000 101 01001 0010011 (0x01D45493)
2C:  11111010110111101100    01010 0110111 (0xFADEC537)
30:  101010111110  01010 000 01010 0010011 (0xABE50513)
34:  0000000 01010 00100 010 00000 0100011 (0x00A22023)
38:  0000000 01010 00100 001 00110 0100011 (0x00A21323)
3C:  0000000 01010 00100 000 01011 0100011 (0x00A205A3)
40:  000000000000  00100 010 01011 0000011 (0x00022583)
44:  000000000000  00100 001 01100 0000011 (0x00021603)
48:  000000000000  00100 000 01101 0000011 (0x00020683)
4C:  000000000000  00100 101 01110 0000011 (0x00025703)
50:  000000000000  00100 100 01111 0000011 (0x00024783)
54:  00000000000000000100    10000 0010111 (0x00004817)
58:  0000000 00011 00100 001 01000 1100011 (0x00321463)
5C:  00000000  00000000 00000000  00000000 (0x00000000)
60:  00000000010000000000    10001 1101111 (0x004008EF)
64:  000000000000  10001 000 01110 1100111 (0x00088767)
68:  000000000100  01111 000 10010 1100111 (0x00478967)
```

_Listing 2. The program from Listing 1 represented in machine code._

This program in hexadecimal format is stored in the file [program.mem](program.mem).

## Steps

1. Carefully study the microarchitectural implementation of the processor core. If you have any questions, consult your instructor.
2. Replace the `program.mem` file in the project's `Design Sources` with the new [program.mem](program.mem) file provided with this lab. This file contains the program from _Listing 1_.
3. Describe the processor core module with the same name and ports as specified in the assignment.
   1. The process of implementing the module is similar to describing the CYBERcobra module, but now the following are added:
      1. the decoder
      2. additional multiplexers and sign-extension units.
   2. It is recommended to first create all the wires that will be connected to the inputs and outputs of each module in the schematic.
   3. Then create the module instances.
   4. Also create the 32-bit I-, U-, S-, B-, and J-type immediate constants and the program counter.
   5. Next, describe the logic that drives the wires created in step 3.2.
   6. Finally, describe the program counter logic.
4. Describe the processor system module that combines the processor core (`processor_core`) with instruction memory and data memory.
   1. Describe the module with the same name and ports as specified in the assignment.
   2. **When instantiating the `processor_core` module inside `processor_system`, you must use the instance name `core` (i.e., instantiate it as: `processor_core core(...`)**.
5. Verify the module using the testbench provided in the file [`lab_07.tb_processor_system.sv`](lab_07.tb_processor_system.sv).
   1. Before running the simulation, make sure the correct top-level module is selected in `Simulation Sources`.
   2. As with the CYBERcobra processor verification, you will not be told whether the test passed or not. You must manually verify, cycle by cycle, that the processor correctly executes the instructions described in _Listing 1_ (refer to the step-by-step instructions of Lab 4). To do this, first calculate what a given instruction should do, then verify that the processor did exactly that.
6. After verifying the processor with the program from _Listing 1_, write your own program for the individual task variant received in Lab 4.
   1. To convert RISC-V assembly code to binary, you can use an online compiler such as: https://venus.kvakil.me. Write the code in the "Editor" tab, then switch to the "Simulator" tab and click the "Dump" button. The binary code will be copied to the clipboard in a format suitable for memory initialization in Vivado; replace the contents of the program.mem file in your project with this code. Using the "Step" and "Run" buttons, you can debug your program in the online simulator before running it on your own processor system. In Lab 14, you will learn how to compile a program on your own without third-party services.
7. Verify the functionality of your digital circuit on the FPGA.

---

<details>
  <summary>Read me when you're done.</summary>
  Congratulations, you've built your first grown-up processor! Now you can say:

 >I can do anything! I built a complete RISC-V processor from scratch, all by myself! What? You don't know what an architecture is? Pfft, rookie! You'll find out when you grow up.

</details>

## References

1. [The RISC-V Instruction Set Manual Volume I: Unprivileged ISA](https://github.com/riscv/riscv-isa-manual/releases/download/20240411/unpriv-isa-asciidoc.pdf).
