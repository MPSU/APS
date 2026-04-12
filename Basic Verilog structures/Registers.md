# Describing Registers in SystemVerilog

Before describing memory, you need to learn how to describe individual registers. A **register** is a device for writing, storing, and reading n-bit binary data and performing other operations on it [1, p. 32]. In modern electronics, a register is most commonly built from D flip-flops. The ALU lab briefly mentioned that both wires and registers are declared using the `logic` type.

```Verilog
logic reg_name;
```

![../.pic/Basic%20Verilog%20structures/registers/fig_01.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_01.drawio.svg)

A register can have multiple inputs and one output. There are two essential inputs without which a register cannot exist: a data input and a clock input. In the figure, these are labeled `D` and `clk`. The optional reset input (`rst`) allows the register contents to be cleared regardless of the data input, and it can operate either synchronously with the clock signal (synchronous reset) or independently of it (asynchronous reset).

In addition, a register may have a write enable input (`enable`), which determines whether the data from the data input will be written to the register, and an optional set input (`set`), which forces the register value to logic one.

A register has a single output. In the figure above, it is labeled `Q`.

It is important to understand that the port names given here are not set in stone — they simply describe the functional purpose. When describing the behavior of a register, you will only operate on the register's name and the signals connected to it.

Since all signals in a digital circuit are carried over nets, it is convenient to think of a wire with the same name as the register as being implicitly connected to the register's output. This means you can use the register's name in subsequent digital logic:

![../.pic/Basic%20Verilog%20structures/registers/fig_02.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_02.drawio.svg)

So, we have placed a register on the schematic canvas — but how do we connect it to some logic? Suppose we have a clock signal and data we want to write:

![../.pic/Basic%20Verilog%20structures/registers/fig_03.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_03.drawio.svg)

This schematic corresponds to the following code:

```Verilog
module reg_example(
  input  logic clk,
  input  logic data,
  output logic reg_data
);

  logic reg_name;

endmodule
```

Clearly, we want to connect the `clk` signal to the register's clock input, `data` to the data input, and the register's output to the `reg_data` output:

![../.pic/Basic%20Verilog%20structures/registers/fig_04.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_04.drawio.svg)

Writing to a register is only possible on the edge of the clock signal. An **edge** is a transition of the signal from zero to one (**rising edge**) or from one to zero (**falling edge**).

The register description, along with the specification of the edge and clock signal, is done using the `always_ff` construct:

```Verilog
always_ff @(posedge clk)
```

Inside this construct, you specify what happens to the register contents. In our case, the data from the `data` input is written:

```Verilog
always_ff @(posedge clk) begin
  reg_name <= data;
end
```

> [!IMPORTANT]
> Note the `<=` operator. In this context, it is not the "less than or equal to" sign — it is the **non-blocking assignment** operator. There is also a **blocking assignment** operator (`=`), which can alter how the circuit is constructed for the same right-hand-side expression. While it may be considered poor educational practice, for now you simply need to remember: **always use the non-blocking assignment operator `<=` when describing writes to a register**. More details are provided in the document "[On the Differences Between Blocking and Non-Blocking Assignments](./Assignments.md)".

In addition, we need to connect the module's output to the register's output. This can be done using the **continuous assignment** operator `assign`, which you are already familiar with.

The complete code describing this schematic is as follows:

```Verilog
module reg_example(
  input  logic clk,
  input  logic data,
  output logic reg_data
);

  logic reg_name;

  always_ff @(posedge clk) begin
    reg_name <= data;
  end

  assign reg_data = reg_name;

endmodule
```

Suppose we want to add write control via `enable` and `reset` signals. This can be done as follows:

```Verilog
module reg_example(
  input  logic clk,
  input  logic data,
  input  logic reset,
  input  logic enable,
  output logic reg_data
);

  logic reg_name;

  always_ff @(posedge clk) begin
    if(reset) begin
      reg_name <= 1'b0;
    end
    else if(enable) begin
      reg_name <= data;
    end
  end

  assign reg_data = reg_name;

endmodule
```

Pay attention to the order of conditions. We first check the **reset** condition, and only then the **write enable** condition.
If the write enable condition is checked first and the reset logic is placed in the `else` block, the register will not be reset when `enable` is asserted (the write operation takes priority over the reset). If the reset is described in a separate `if` block rather than in an `else` block, undefined behavior may occur: it becomes impossible to determine what will be written to the register if both `reset` and `enable` arrive simultaneously. Therefore, when a reset signal is present, all other write logic must be placed inside the `else` block.

Furthermore, EDA tools recognize the pattern used to describe a circuit element and, once recognized, implement it as the designer intended. For this reason, when describing a register, the reset signal (if used) must always be described first, followed by all other write logic in the `else` block.

The resulting schematic of a register with reset and write enable:

![../.pic/Basic%20Verilog%20structures/registers/fig_05.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_05.drawio.svg)

There is one more important rule to know when describing a register:

**Assignment to a register may only occur within a single `always` block.**

Even if the EDA tool does not immediately report an error, it will eventually appear during synthesis as a message related to **"multiple drivers"**.

Combinational logic that precedes the register can also be described inside the register's assignment block. For example, the following schematic:

![../.pic/Basic%20Verilog%20structures/registers/fig_06.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_06.drawio.svg)

can be described as:

```Verilog
module reg_example(
  input  logic clk,
  input  logic A,
  input  logic B,
  input  logic reset,
  input  logic enable,
  output logic reg_data
);

  logic reg_name;

  always_ff @(posedge clk) begin
    if(reset) begin
      reg_name <= 1'b0;
    end
    else if(enable) begin
      reg_name <= A & B;
    end
  end

  assign reg_data = reg_name;

endmodule
```

However, this is merely a shorthand. If you know how to describe a register with a single wire connected to its data input, you can still describe this schematic:

```Verilog
module reg_example(
  input  logic clk,
  input  logic A,
  input  logic B,
  input  logic reset,
  input  logic enable,
  output logic reg_data
);

  logic reg_name;     // Note that even though both
  logic ab;           // reg_name and ab are declared as logic,
                      // ab will become a wire and reg_name a register
                      // (due to the continuous assignment for ab and the
                      // always_ff block for reg_name)

  assign ab = A & B;

  always_ff @(posedge clk) begin
    if(reset) begin
      reg_name <= 1'b0;
    end
    else if(enable) begin
      reg_name <= ab;
    end
  end

  assign reg_data = reg_name;

endmodule
```

This is why it is so important to understand the fundamental way of describing a register.

Moreover, from the synthesizer's perspective, this description is easier to synthesize because it does not need to separate the combinational and synchronous parts from within a single `always` block.

In general, a register is a multi-bit construct (in the earlier example, a 1-bit register could be represented as a simple D flip-flop).
Creating a multi-bit register differs little from creating a multi-bit wire, and the write logic for a multi-bit register is identical to that of a 1-bit register:

```Verilog
module reg_example(
  input  logic        clk,
  input  logic [7:0]  data,
  output logic [7:0]  reg_data
);

  logic [7:0] reg_name;

  always_ff @(posedge clk) begin
    reg_name <= data;
  end

  assign reg_data = reg_name;

endmodule
```

## Chapter Summary

1. A [register](https://en.wikipedia.org/wiki/Hardware_register) is a basic storage element that retains its state as long as the circuit is powered.
2. A register is declared using the `logic` type; if needed, the bit width is specified after the type.
3. The write logic for a register is described using the `always_ff` block, whose parentheses specify the clock signal and the edge on which writing occurs, as well as the reset signal (in the case of an asynchronous reset).
4. A register can have various control signals: set, reset, and write enable. The logic for these control signals is part of the register's write logic and is also described inside the `always_ff` block.
5. When describing register write logic, the **non-blocking assignment** operator `<=` must be used.
6. Write logic for a register must not be described in more than one `always` block (in other words, the assignment operation for each register may only appear in a single `always` block).

## Test Yourself

How would you describe the schematic shown below in SystemVerilog?

![../.pic/Basic%20Verilog%20structures/registers/fig_07.drawio.svg](../.pic/Basic%20Verilog%20structures/registers/fig_07.drawio.svg)

## References

1. Sh. Gabrielyan, E. Vakhtina / Electrical Engineering and Electronics. Methodological Guidelines. — Stavropol: Argus, 2013
