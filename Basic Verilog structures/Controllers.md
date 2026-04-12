# Example of Developing a Peripheral Device Controller Module

To better understand what is required in the peripheral devices lab, let us walk through the process of developing a block diagram (not a SystemVerilog description) for an LED controller.

First, we reproduce the relevant excerpt from the controller specification (the general section "[Peripheral Device Controller Descriptions](../Labs/13.%20Peripheral%20units/README.md#описание-контроллеров-периферийных-устройств)" and the subsection "[LEDs](../Labs/13.%20Peripheral%20units/#Светодиоды)"):

## Controller Specification

### General Terms

1. A "**write request** to address `0xADDRESS`" refers to the combination of the following conditions:
   1. A rising edge of `clk_i` occurs.
   2. The input `req_i` is asserted to `1`.
   3. The input `write_enable_i` is asserted to `1`.
   4. The input `addr_i` holds the value `0xADDRESS`
2. A "**read request** to address `0xADDRESS`" refers to the combination of the following conditions:
   1. A rising edge of `clk_i` occurs.
   2. The input `req_i` is asserted to `1`.
   3. The input `write_enable_i` is asserted to `0`.
   4. The input `addr_i` holds the value `0xADDRESS`

Note that a **read request** must be handled **synchronously** (output data must be produced on the rising edge of `clk_i`), in the same way as the read port of the data memory was implemented in [Lab 6](../Labs/06.%20Main%20memory/).

The following notation is used to describe the supported access modes for each address:

- R — **read-only** access;
- W — **write-only** access;
- RW — **read and write** access.

When there is no **read request**, the value on `read_data_o` must not change (the same behavior was implemented during data memory development).

Receiving a **write** or **read request** does not necessarily mean the controller must execute it. If a request is made to an address that does not support the requested operation (e.g., a **write request** to a read-only address), the request must be ignored. For a **read request** to an unsupported address, the value on `read_data_o` must remain unchanged.

When a write is performed in response to a valid request, the data from `write_data_i` must be written into the register associated with `addr_i` (if the register width is less than the width of `write_data_i`, the upper bits of the written data are discarded).

When a read is performed in response to a valid request, on the rising edge of `clk_i` the data associated with `addr_i` must be placed on the output `read_data_o` (if the signal width is less than the width of `read_data_o`, the returned data must be zero-extended in the upper bits).

### LEDs

LEDs are the simplest output device. To make the assignment more interesting, a register controlling the LED output mode has been added.
Here is the module prototype you need to implement:

```Verilog
module led_sb_ctrl(
/*
    Part of the module interface responsible for connection to the system bus
*/
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic        req_i,
  input  logic        write_enable_i,
  input  logic [31:0] addr_i,
  input  logic [31:0] write_data_i,
  output logic [31:0] read_data_o,

/*
    Part of the module interface responsible for connection to the peripheral
*/
  output logic [15:0] led_o
);

logic [15:0]  led_val;
logic         led_mode;

endmodule
```

This module must drive the output signal `led_o` with the value from register `led_val`. Reading and writing register `led_val` is performed at address `0x00`.

Register `led_mode` controls the LED output mode. When this register equals one, the LEDs must "blink" with the output value. Blinking means: drive the value from `led_val` onto `led_o` for one second (the LEDs whose corresponding bits in `led_o` are one will light up), then drive `led_o` to zero for one second. Reading and writing register `led_mode` is performed at address `0x04`.

Timekeeping can be implemented with a simple counter that increments by 1 each clock cycle and resets when it reaches a certain value to start counting again. Knowing the clock frequency, it is straightforward to determine the counter limit. At a clock frequency of 10 MHz, there are 10 million cycles per second. This means that at this frequency, after one second the counter will equal `10⁷-1` (counting from zero). However, it is more convenient to count not to `10⁷-1` (which would be an obvious and correct solution), but to `2*10⁷-1`. In this case, the MSB of the counter inverts its value every second, which can be used directly to implement the blinking logic.

It is important to note that the counter must operate only when `led_mode == 1`; otherwise, the counter must be held at zero.

Note that address `0x24` is the reset address. Upon a **write request** of value `1` to this address, you must reset registers `led_val`, `led_mode`, and all auxiliary registers you created. To implement the reset, you may either create a dedicated register `led_rst` that is written to, with the reset occurring when this register becomes one (in which case you must also reset this register), or create a plain wire that goes high when all specified conditions are met (the conditions of the **write request**, the reset address, and the written data value equaling one).

Controller address space:

|Address|Access Mode|Valid Values|                       Functional Description                                   |
|-------|-----------|------------|--------------------------------------------------------------------------------|
|0x00   | RW        | [0:65535]  | Read and write to register `led_val`, which controls the data output to the LEDs |
|0x04   | RW        | [0:1]      | Read and write to register `led_mode`, which controls the LED blinking mode    |
|0x24   | W         |  1         | Write reset signal                                                             |

## Controller Circuit Implementation

First, add the module's inputs and outputs to the block diagram:

![../.pic/Basic%20Verilog%20structures/controllers/fig_01.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_01.drawio.svg)

The specification introduces the concepts of **read request** and **write request**. Let us create auxiliary wires that signal when a **read request** or **write request** has occurred:

![../.pic/Basic%20Verilog%20structures/controllers/fig_02.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_02.drawio.svg)

Additionally, the specification defines the controller's address space. Let us create auxiliary signals that indicate whether the current address corresponds to one of the controller's registers:

![../.pic/Basic%20Verilog%20structures/controllers/fig_03.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_03.drawio.svg)

With the preparatory work done, let us begin with the reset logic for this controller. A reset can occur in two cases: when `rst_i == 1`, or when a **write request** of value one is made to address `0x24`. Let us create an auxiliary wire `rst` that is high when either of these events occurs. This signal will reset all registers created inside this module.

![../.pic/Basic%20Verilog%20structures/controllers/fig_04.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_04.drawio.svg)

Continuing the controller description, let us create the first **architectural register** — `led_val`. Writing to this register is only permitted on a write request to address `0x00`. Let us create an auxiliary signal `val_en` that is high only when these conditions are met:

![../.pic/Basic%20Verilog%20structures/controllers/fig_05.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_05.drawio.svg)

Now implementing register `led_val` becomes a straightforward task, since we have:

- the register reset signal `rst`;
- the register write-enable signal `val_en`;
- the write data signal `write_data_i` (from which we take only the lower 16 bits).

![../.pic/Basic%20Verilog%20structures/controllers/fig_06.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_06.drawio.svg)

Similarly, implement the second **architectural register** `led_mode`:

![../.pic/Basic%20Verilog%20structures/controllers/fig_07.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_07.drawio.svg)

These two registers must control the behavior of the output signal `led_o` as follows:

1. When `led_mode == 0`, the output `led_o` must carry the value of `led_val`;
2. When `led_mode == 1`, the output `led_o` must cyclically alternate between `led_val` and `16'd0` with a period of one second.

To implement timekeeping, we need an auxiliary **non-architectural register** `cntr`, which acts as a simple resettable counter. We know that our circuit's clock runs at 10 MHz. Incrementing the counter by one each cycle, after one second the counter will reach 10 million. The first instinct might be to count to 10 million and then reset to zero, but this creates complications for the subsequent implementation. It is much more convenient to count to 20 million instead (the full period of alternating between `led_val` and `16'd0`). In this case, we only need to add a multiplexer output condition:

- while the counter value is less than 10 million, `led_o` outputs `led_val`
- otherwise, `led_o` outputs `16'd0`.

The counter behavior is therefore described as follows:

- the counter resets in the following cases:
  - a reset occurred (`rst == 1`);
  - LED blinking was disabled (`led_mode == 0`);
  - the counter reached 20 million (`cntr >= 32'd20_000_000`);
- in all other cases, the counter increments its value.

![../.pic/Basic%20Verilog%20structures/controllers/fig_08.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_08.drawio.svg)

The final step in describing the controller is adding the logic that controls the output signal `read_data_o`.

The following requirements apply to this signal:

- changes to this signal must be **synchronous** (i.e., a register must precede the output signal);
- upon a **read request** to a supported address, this signal must take the value of the register associated with that address (zero-extended to the full output width);
- in the absence of a **read request**, or on a read request to an unsupported address, the register must retain its current value.

To keep the register's value between **read requests** to supported addresses, we add an enable signal to it, and drive its data input from a multiplexer that selects among the available read data sources.

The final circuit is thus:

![../.pic/Basic%20Verilog%20structures/controllers/fig_09.drawio.svg](../.pic/Basic%20Verilog%20structures/controllers/fig_09.drawio.svg)
