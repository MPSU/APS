# Describing Multiplexers in SystemVerilog

**A multiplexer** is a device that selects one of several input signals and forwards it to a single output depending on the value of a control input.

In other words, a multiplexer is a switch that connects the output to one of many inputs.

![../.pic/Basic%20Verilog%20structures/multiplexor/fig_01.drawio.svg](../.pic/Basic%20Verilog%20structures/multiplexors/fig_01.drawio.svg)

Let us start with a simple two-input multiplexer. Suppose we need to forward one of the signals — `D0` or `D1` — to output `Y`, depending on the value of control signal `S`: when `S==0`, signal `D0` is driven to `Y`; otherwise, `D1` is driven.

![../.pic/Basic%20Verilog%20structures/multiplexors/fig_02.drawio.svg](../.pic/Basic%20Verilog%20structures/multiplexors/fig_02.drawio.svg)

In SystemVerilog this can be described in several ways. The first is using the **[ternary conditional operator](https://ru.wikipedia.org/wiki/Тернарная_условная_операция)**:

## Ternary Conditional Operator

<details>

<summary>About the ternary conditional operator</summary>

Operators differ in their **[arity](https://ru.wikipedia.org/wiki/Арность)** (the number of operands they take):

- unary (one operand), example: `-a`;
- binary (two operands), example: `a+b`;
- ternary (three operands), example: `cond ? if_true : if_false`;
- and others.

Although any operator that takes three operands is technically ternary, the term usually refers to the **ternary conditional operator**, which works as follows:

```text
<condition> ? <value_if_condition_is_true> : <value_if_condition_is_false>
```

The first operand is a condition (any expression that evaluates to 1 or 0). It is followed by a question mark (the part of the ternary operator that separates the first operand from the second). Next comes the expression that will be the result of the ternary conditional operator if the condition is true. This is followed by a colon (the part of the ternary conditional operator that separates the second operand from the third). Finally, the expression that will be the result if the condition is false.

Example in C++:

```c++
a = b+c >= 5 ? b+c : b+d;
```

First, the first operand (`b+c >= 5`) is evaluated. If this expression is true (equals one), then variable `a` is assigned the value of the second operand (`b+c`); otherwise, `a` is assigned the value of the third operand (`b+d`).
</details>

```Verilog
logic Y;
assign Y = S==1 ? D1 : D0;
```

This expression states that if `S==1`, then `Y` is assigned the value of `D1`; otherwise, the value of `D0`.

![../.pic/Basic%20Verilog%20structures/multiplexors/fig_03.drawio.svg](../.pic/Basic%20Verilog%20structures/multiplexors/fig_03.drawio.svg)

A multiplexer can also be described using an `if-else` construct inside an `always` block.

> The following section contains key concepts that may be difficult to grasp at first. It is very important to understand and remember what is written there, and to work through the code listings provided.

<br><br>

---

## The always Block

The `always` block is a special block that allows describing both combinational and sequential circuits (see the document "[Sequential Logic](../Introduction/Sequential%20logic.md)"), using more complex constructs such as `if-else` and `case`. In fact, SystemVerilog provides not only the general-purpose `always` block, which can describe any type of logic, but also several specialized blocks for combinational, synchronous sequential, and asynchronous sequential logic respectively:

- always_comb
- always_ff
- always_latch

A multiplexer can be described in any of these blocks; the only difference is what the multiplexer output will be connected to: a wire, a register, or a latch.

Depending on the type of `always` block used, one of two assignment operators is required: **blocking assignment** (`=`) or **non-blocking assignment** (`<=`). The differences between these assignment types are described in detail in [this document](Assignments.md). Until you read it, remember the following:

- inside `always_ff` and `always_latch` blocks, use the non-blocking assignment operator (`<=`);
- inside `always_comb` blocks, use the blocking assignment operator (`=`).

---

> Do not move past the highlighted section above until you fully understand it. Without mastering these features of SystemVerilog, you will encounter many errors in the future.

<br><br>

## The if-else Block

Describing a multiplexer using `if-else` is similar to using the ternary operator. Whereas in the ternary operator the control signal is the first operand separated by the `?` operator, in this construct the control signal is placed in parentheses after the keyword `if`.

The assignment for the signal that should appear at the output when the control signal equals one follows (corresponding to the value before the `:` operator in the ternary form).

The assignment for the signal that should appear at the output when the control signal equals zero is then placed in the `else` block (corresponding to the value after the `:` operator in the ternary form).

```Verilog
logic Y;
always_comb begin // 1) always_comb is used because we want to connect
                  // the multiplexer output to a wire
  if(S) begin     // 2) if-else can only be placed inside an always block.
    Y = D1;       // 3) The blocking assignment operator is used.
  end else begin
    Y = D0;
  end
end
```

It is also important to remember that assignment to a signal is allowed in **only one** always block.

Incorrect:

```Verilog
logic Y;
always_comb begin
  if(S==1) begin
    Y = D1;
  end
end

always_comb begin
  if(S==0) begin // It is not allowed to assign
    Y = D0;      // the same signal (Y) in multiple
  end            // always blocks!
end
```

Violating this rule will eventually (perhaps not immediately, but inevitably) cause an error related to **multiple drivers**.

Be **very careful** when using this construct. It is deceptively similar to a conditional block in programming languages, which may tempt you to use it the same way. This is not correct. Note that this construct is referred to strictly as an `if-else` block. When describing a multiplexer, every `if` block must have a corresponding `else` block, just as the ternary operator requires two output operands. If the `else` block is omitted when describing a multiplexer, the output will have only one driver, and a **latch** will be inferred. Latches are described in more detail [here](Latches.md).

There are situations where an `if` block can be used without a corresponding `else` block (for example, when describing decoders or write-enable signals). However, this never applies when describing multiplexers.

## The case Block

A multiplexer can also be described using the **case construct**. The `case` block is better suited for multiplexers with more than two inputs (since `if-else` would require nested branching).

The `case` construct is a multi-way branching tool that compares the value of a given expression against a set of alternatives and executes the matching branch. Like `if-else`, the `case` block must cover all possible combinations of the control signal (otherwise a latch will be inferred). To handle any combination not explicitly listed, the `case` construct supports a `default` branch. This construct visually resembles the `switch-case` operator in C, but keep in mind that it is used not to write a program, but to describe hardware — in particular **multiplexers**/**demultiplexers** and **decoders**.

**The `case` construct, like `if-else`, can only be described inside an `always` block.**

A two-input multiplexer implemented with `case` may look like this:

```Verilog
logic Y;
always_comb begin
  case(S)           // Describe a case block where the value of signal S
                    // is compared against its possible values
    1'b0: Y = D0;   // If S==0, then Y = D0
    1'b1: Y = D1;
  endcase           // Every case must end with endcase
end                 // (just as every begin must end with end)
```

Let us consider a more complex example and describe the following circuit:

![../.pic/Basic%20Verilog%20structures/multiplexors/fig_04.drawio.svg](../.pic/Basic%20Verilog%20structures/multiplexors/fig_04.drawio.svg)

Here an 8-to-1 multiplexer is used. The control signal `S` is 3 bits wide. In the `case` block, we enumerate all possible values of `S` and describe the multiplexer output.

```Verilog
module case_mux_ex(
  input  logic        A,
  input  logic        B,
  input  logic        C,
  input  logic        D,
  input  logic [2:0]  S,

  output logic        Y

);
  always_comb begin
    case(S)
      3'b000:  Y = A;
      3'b001:  Y = C | B;      // inside a case block, you can multiplex
                               // not only wires but also logical expressions
      3'b010:  Y = (C|B) & D;
      /*
        Note that signal S is 3 bits wide.
        This means there are 8 possible combinations of its bits.
        Only 3 out of 8 combinations are described above.
        If all remaining combinations should produce a single
        "default" value at the multiplexer output, use the
        special "default" branch:
      */
      default: Y = D;
    endcase
  end
endmodule
```

## Indexing Operator

Suppose we need to multiplex a very large number of signals — for example, individual bits of a 1024-bit bus. Writing a `case` with 1024 branches would be impractical. In this case, the `[]` operator can be used, which you likely know as the "array indexing operator" from C-like languages. It works intuitively:

- before the operator, specify the name of the array or vector (i.e., a memory or bus) to be indexed;
- inside the square brackets, specify the index — either a constant or an expression using other signals.

In the context of multiplexing 1024 bits, the operator can be used as follows:

```Verilog
logic [1023:0] bus1024;
logic [   9:0] select;

logic          one_bit_result;

assign one_bit_result = bus1024[select];
```

The `[]` operator for implementing multiplexers will be used extensively when implementing various memory structures.

## Chapter Summary

1. A multiplexer is a **combinational** block that forwards one of several input signals to the output.
2. A multiplexer can be described in multiple ways, including:
   1. using the [ternary conditional operator](#ternary-conditional-operator);
   2. using the [`if-else`](#the-if-else-block) construct inside an [`always`](#the-always-block) block;
   3. using the [`case`](#the-case-block) construct inside an [`always`](#the-always-block) block;
   4. using the [`[]` operator](#indexing-operator).
3. To avoid unintended [latches](Latches.md) when describing a multiplexer, ensure that every `if` block has a corresponding `else` block, and that every `case` block covers all combinations of the control signal (if needed, the remaining combinations can be covered with `default`). An unintended latch in a design degrades timing characteristics, wastes resources, and causes unpredictable behavior due to unwanted signal retention.
4. It is important to note that `if-else` and `case` blocks can be used for purposes other than describing multiplexers.
5. In the scope of these lab assignments, `if-else` and `case` constructs may only be used inside an [`always`](#the-always-block) block. When working with this block, keep the following in mind:
   1. There are several types of `always` blocks: `always_comb`, `always_ff`, `always_latch`, which determine what the described logic will be connected to: a wire, a register, or a latch, respectively. In these lab assignments, you will use `always_ff` and `always_comb`, where:
      1. inside `always_ff`, use the non-blocking assignment operator (`<=`);
      2. inside `always_comb`, use the blocking assignment operator (`=`).
   2. Assignment to any given signal is allowed in **only one** always block. Two different signals may be assigned either in the same always block or each in a separate one, but assigning the same signal in two different always blocks is not permitted.

---

## Test Yourself

How would you describe the following circuit in SystemVerilog?

![../.pic/Basic%20Verilog%20structures/multiplexors/fig_05.drawio.svg](../.pic/Basic%20Verilog%20structures/multiplexors/fig_05.drawio.svg)
