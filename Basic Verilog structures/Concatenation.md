# Concatenation (Signal Merging)

Concatenation allows assigning a multi-bit signal the "join" of several lower-width signals, or conversely, assigning a higher-width signal to a group of lower-width signals.

The concatenation operator has the following form: `{sig1, sig2, ..., sign}`.

Suppose we have the following set of signals:

![../.pic/Basic%20Verilog%20structures/concatenation/fig_01.drawio.svg](../.pic/Basic%20Verilog%20structures/concatenation/fig_01.drawio.svg)

```Verilog

logic a;
logic b;
logic [7:0] c;
logic [1:0] d;

logic [5:0] e;
```

And we want the wire `e` to receive the following signals:

- the MSB of signal `e` receives signal `a`
- the next bit receives signal `b`
- the next 2 bits receive bits `[4:3]` of signal `c`
- the 2 LSBs receive signal `d`

![../.pic/Basic%20Verilog%20structures/concatenation/fig_02.drawio.svg](../.pic/Basic%20Verilog%20structures/concatenation/fig_02.drawio.svg)

This can be done using 4 continuous assignments:

```Verilog
logic a;
logic b;
logic [7:0] c;
logic [1:0] d;

logic [5:0] e;

assign e[5]   = a;
assign e[4]   = b;
assign e[3:2] = c[4:3];
assign e[1:0] = d;
```

or with a single assignment using concatenation:

```Verilog
logic a;
logic b;
logic [7:0] c;
logic [1:0] d;

logic [5:0] e;

assign e = {a, b, c[4:3], d};
```

The reverse is also possible. Suppose we want to drive individual wires from separate bits of signal `e`:

![../.pic/Basic%20Verilog%20structures/concatenation/fig_03.drawio.svg](../.pic/Basic%20Verilog%20structures/concatenation/fig_03.drawio.svg)

```Verilog
logic a;
logic b;
logic [7:0] c;
logic [1:0] d;

logic [5:0] e;

assign a      = e[5];
assign b      = e[4];
assign c[4:3] = e[3:2];
assign d      = e[1:0];
```

This operation can also be expressed as a single concatenation:

```Verilog
logic a;
logic b;
logic [7:0] c;
logic [1:0] d;

logic [5:0] e;

assign {a, b, c[4:3], d} = e;
```

Additionally, concatenation can be used for **signal replication**. Replication is expressed as:

```Verilog
{a, {replication_count{signal_to_replicate}} ,b}
```

For example, to assign three copies of bits `[4:3]` of signal `c`, followed by signals `a` and `b`:

```Verilog
logic a;
logic b;
logic [7:0] c;

logic [7:0] e;

assign e = { {3{c[4:3]}}, a, b};
```

## Chapter Summary

The concatenation operator can be used to group and replicate signals on either side of an assignment:

- it can be used to assign a group of lower-width signals to a higher-width signal
- it can be used to assign the corresponding bits of a higher-width signal to a group of lower-width signals.
