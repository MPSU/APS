# Sequential Logic

## Classification of Digital Logic

Digital logic is divided into **combinational** and **sequential** logic.

**Combinational logic** (or "memoryless logic") is digital logic whose outputs depend only on its inputs. The same set of input stimuli will always produce the same result. Combinational logic can always be represented as a truth table (or a logic function) of all its outputs in terms of its inputs.

In contrast to combinational logic, there also exists **sequential logic**, or "logic with memory" — digital logic whose outputs depend not only on its inputs, but also on its internal state.

The simplest example of combinational logic is any logic gate, such as XOR (_fig. 1 (a)_). This combinational circuit will always output `0` when both of its inputs are equal, and `1` otherwise.

![../.pic/Introduction/Sequential%20logic/fig_01.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_01.drawio.svg)

_Figure 1. Example of a combinational (a) and a sequential (b) circuit._

Now suppose that one of the XOR inputs is a memory cell that stores the previous value produced by that gate (_fig. 1 (b)_). The circuit's outputs now depend not only on what we apply to the input, but also on what is currently held in the memory cell — and most importantly, applying the same input stimulus can now yield different results.

Assume the memory cell is initially set to zero. First, we apply `0` to the input. Since both inputs are equal to `0`, the output is `0` and the memory cell retains its value. Next, we apply `1` — the output becomes `1` and is stored in the memory cell. We then apply `0` again; unlike the first time, the output is now `1`, because the XOR inputs are unequal. Applying `1` once more yields `0` at the output.

As you can see, the result of sequential logic depends on the **sequence** of input stimuli applied, whereas combinational logic depends on the **combination** of its current inputs.

Sequential logic is divided into **synchronous** and **asynchronous**.

**Synchronous logic** is logic that updates its state (the contents of its memory cells) simultaneously (**synchronously**) with the edge of a clock signal\*. **Asynchronous sequential logic**, in turn, is logic that can update its state **asynchronously** (i.e., independently of a clock edge). There also exist synchronous circuits with asynchronous preset/reset signals.

Combinational logic is inherently asynchronous; therefore, depending on context, "asynchronous logic" may refer either to combinational logic or to sequential logic whose state can change without being tied to a clock edge.

> [!Info]
> Some sources also refer to logic that operates on the level (rather than the edge) of a single clock source as synchronous logic [1, p. 119].

## Bistable Cells

A **bistable cell** is a static memory element capable of holding one of two stable states corresponding to the digital values "0" or "1".

**Static memory** is a type of memory that retains data indefinitely as long as power is supplied, without requiring refresh cycles (unlike **dynamic memory**, which uses capacitors for storage and requires periodic data refresh to prevent loss).

Consider the simplest static memory cell shown in _fig. 2_, which is capable of storing 1 bit of information.

![../.pic/Introduction/Sequential%20logic/fig_02.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_02.drawio.svg)

_Figure 2. The simplest static memory cell._

This cell consists of a loop of two inverters in which the stored value is "latched". A signal inverted twice equals its original value, and as it passes through each inverter the voltage level is refreshed, thereby maintaining the voltage levels that represent the logic values. The main drawback of such a cell is that it requires additional hardware to write new data into it.

To add write capability, OR gates can be placed before the inverters (which, together with the inverters, form NOR gates).

The result is an **RS latch** — the bistable cell shown in _fig. 3_.

## RS latch

![../.pic/Introduction/Sequential%20logic/fig_03.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_03.drawio.svg)

_Figure 3. Circuit and truth table of the RS latch. X indicates that the result in that row is independent of the stored value._

An RS latch is a bistable cell with two control inputs: `R` (reset) and `S` (set), and two outputs: `Q` and `Q̅`. `Q̅` is the complement of `Q`. An RS latch built from NOR gates operates as follows:

1. If `R=1` and `S=0`, the output of the upper NOR gate (and therefore output `Q`) is `0` regardless of its second input. This output, together with input `S`, drives the lower NOR gate, which produces `1` (at output `Q̅`) since both of its inputs are `0`. This `1` is fed back to the second input of the upper NOR gate, so that even if `R` returns to `0`, the `1` on its second input reproduces the same behaviour, locking the stable state `Q=0` inside the flip-flop.
2. If `R=0` and `S=1`, the circuit operates in the opposite manner: since `1` from input `S` drives the lower gate, output `Q̅` is `0` regardless of the lower NOR gate's second input. This `0` is applied to the second input of the upper NOR gate, and since both of its inputs are `0`, the output of that gate (output `Q`) is `1`, which feeds back to the lower NOR gate's input, locking the stable state `Q=1` inside the flip-flop.
3. Therefore, when both inputs are simultaneously `0`, the RS latch retains its previous value.

The drawback of this flip-flop is that it has a **forbidden** input combination. For an RS latch built from NOR gates, this forbidden combination is `R=1` and `S=1`. Even from a functional standpoint, this combination makes no sense: who would want to simultaneously reset an RS latch to 0 and set it to 1? Nevertheless, here is what happens when this combination is used:

4. If both inputs are simultaneously `1`, both outputs Q and Q̅ will be `0`, which violates the latch logic since Q̅ should be the complement of Q. Moreover, if both inputs are then **simultaneously** returned to `0`, the RS latch enters an unstable (racing) state, and the outputs may oscillate indefinitely. While the RS latch was in the forbidden state, outputs `Q` and `Q̅`, both equal to `0`, were fed back to the inputs of both NOR gates. If both `R` and `S` are simultaneously returned to `0`, both gate inputs become `0`, causing both gates to output `1`, which feeds back to their inputs, after which they output `0`, and this continues until one of the signals in the feedback loop wins the race and the RS latch settles into a stable state of `0` or `1`.

To eliminate the forbidden state of the RS latch, the D latch was devised.

## D Latch

A D latch is a bistable memory cell with inputs `D` (Data) and `E` (enable). The enable input is sometimes called clk (clock) or G (gated), which does not affect its functional role. When `E` is `1`, the D latch "captures" data from input `D`. When `E` is `0`, the D latch holds the previously captured data.

A D latch can be built on top of an RS latch by adding logic that prevents the forbidden state from occurring (_fig. 4_).

![../.pic/Introduction/Sequential%20logic/fig_04.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_04.drawio.svg)

_Figure 4. Circuit and truth table of the D latch._

The D latch operates as follows. When `E` is `0`, the AND gates drive their outputs to `0` regardless of the second input, and the RS latch transitions to its hold state. In this situation the D latch is said to be "closed", or "opaque". When `E` is `1`, the AND gates placed before the RS latch inputs pass the value of their second input to the output. The complementary signals `!D` and `D` are applied to the second inputs of these gates, which prevents both `R` and `S` from being `1` simultaneously. In this case the value from input `D` enters the RS latch, and the D latch is said to be "open" (it transitions to the "transparent" state). While the latch is transparent, data from input `D` passes directly to output `Q`.

Although the D latch eliminates the main drawback of the RS latch, it is not the most reliable bistable memory cell too. The problem is that the D latch passes data from input `D` to the output for the entire time it is transparent. This means it propagates all transient glitches on the `D` signal, which subsequent portions of the digital circuit will react to. As a result, transients originating at the circuit inputs propagate throughout the entire design, making it practically impossible to determine at what moments in time the circuit output contains a valid result. It would be far more convenient to capture data instantaneously, at the moment when input `D` has already settled to a stable value, thereby cutting off transients from all preceding stages at each memory element. The D flip-flop (D flip-flop) is exactly such a memory element.

## D Flip-Flop

A D flip-flop is a static memory element that captures data from input `D` **at the moment the control signal transitions from zero to one** (or from one to zero). This signal is called the **clock signal** (or **clock**) and is denoted clk.

_Figure 5_ shows how a D flip-flop is constructed from two D latches.

![../.pic/Introduction/Sequential%20logic/fig_05.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_05.drawio.svg)

_Figure 5. Circuit and truth table of the D flip-flop._

The D flip-flop shown in _fig. 5_ operates on the principle that the enable signal `E` of one latch is the complement of the enable signal `E` of the other. This means that while one latch is transparent and accepting data from the input, the other is opaque and not accepting data. At the moment the clock transitions from `0` to `1`, the master latch becomes opaque to new data from input `D`, and the data "latched" inside it passes into the slave latch that has just opened. Although the slave latch remains transparent for the entire time `clk = 1`, the data inside it remains stable because the master latch output can no longer change.

The bistable cell circuits described above are more of a mathematical model of memory elements — they serve to explain the operating principle more clearly. If your technology allows you to implement AND, OR, and NOT gates, you can certainly implement such elements. Moreover, by exploiting the characteristics of a specific technology, these circuits can be implemented more efficiently. A D latch, for example, can be implemented as the circuit shown in _fig. 6_.

![../.pic/Introduction/Sequential%20logic/fig_06.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_06.drawio.svg)

_Figure 6. Configurable memory cell of the Xilinx XC2064 FPGA [[2, p. 2-63](https://archive.org/details/programmablegate00xili/page/n93/mode/2up)]._

## Metastability

As mentioned earlier, designing efficient digital circuits requires consideration of the analog characteristics of the technology in which those circuits will be implemented. Let us analyze the simplest bistable cell built from two inverters by examining _fig. 7_. _Figure 7 (a)_ shows the transfer function U<sub>out</sub> = T(U<sub>in</sub>) of an inverter. The horizontal axis represents the input voltage applied to the inverter, and the vertical axis represents its output voltage. Applying 0 V (corresponding to digital value `0`) to the input of an inverter described by such a transfer function yields 3 V (corresponding to digital value `1`) at the output, and vice versa: applying 3 V yields approximately 0 V at the output.

Since in a bistable cell the output of one inverter drives the input of the other, it is convenient to superimpose the transfer function plots of both inverters so that the input voltage of one inverter shares the same axis as the output voltage of the other, as shown in _fig. 7 (b)_. The intersection points of the curves on this plot are equilibrium points at which the input and output voltages of both inverters are mutually consistent.

![../.pic/Introduction/Sequential%20logic/fig_07.svg](../.pic/Introduction/Sequential%20logic/fig_07.svg)

_Figure 7. Transfer functions for: a) a single CMOS inverter; b) a pair of inverters connected in a bistable loop [3, p. 497]._

As you can see, there are three intersection points rather than two. Two of these are labeled as **stable** and correspond to the familiar digital values 1 (at 3 V) and 0 (at 0 V). The third equilibrium point is labeled **metastable** and lies approximately midway between the two stable values. Indeed, according to the plot, applying approximately 1.5 V to the input produces exactly the same voltage at the output, which is then applied to the second inverter's input, and so on, causing the loop to remain in this state for an indeterminate period. This condition is called the **metastable state** and is an inherent property of any bistable cell implemented in electronic hardware.

Metastability is traditionally explained using the analogy of a ball on a hill (_fig. 8_). Suppose the ball is resting at the bottom of the left slope. Applying sufficient force to the right will cause the ball to roll over the hill and come to rest on the opposite slope (walls are placed at the bottom of each slope for convenience, so the ball always stops at the same point). Applying insufficient force causes the ball to roll partway up the hill and roll back to its starting position. However, if you are sufficiently "lucky" and "precise", you can apply exactly enough force to push the ball to the top of the hill without it rolling off. The ball may remain at the top for an indeterminate amount of time, but any slight disturbance — a gentle breeze from the wing of a passing butterfly, a distant earthquake, or any other exotic cause you care to imagine — can send the ball rolling in either direction.

![../.pic/Introduction/Sequential%20logic/fig_08.svg](../.pic/Introduction/Sequential%20logic/fig_08.svg)

_Figure 8. A mechanical analogy for metastability [3, p. 498]._

Returning to _fig. 7 (b)_: suppose the inverter is in the metastable state and a random noise event slightly perturbs the voltage at the input of one of the inverters. This perturbation is amplified at the inverter's output and applied to the second inverter's input, where it is amplified again and fed back to the first inverter's input, and so on, until the loop ultimately settles at the upper equilibrium point.

If the disturbance occurs while the bistable cell is in a stable state, its state will not change. Suppose the bistable cell is storing the value `1`, meaning 0 V is applied to the first inverter's input, and a disturbance shifts this voltage to 1 V (an extremely large deviation for such a digital circuit, well outside the normal operating range). Drawing a vertical line to its intersection with the black curve gives the output voltage of the first inverter and the input voltage of the second. Drawing a horizontal line from that point to its intersection with the blue curve gives the output voltage of the second inverter and the input voltage of the first. By that point the first inverter's input has already returned to near-zero voltage. This is precisely why the two outer intersection points are called **stable**: as long as power is applied, the cell remains in that state indefinitely until a sufficiently large disturbance occurs to cause a transition.

In the metastable case, we cannot predict the specific duration for which the cell will remain in that state — it is a random variable for which only probabilistic estimates can be made. For example, one might say: "the probability that the bistable cell will exit the metastable state within 100 ms is far greater than the probability that it will still be in that state after 100 seconds."

Thus, metastability is a phenomenon that arises when the operating conditions of digital elements are violated. In normal circumstances it is an undesirable effect (unless you intend to use your circuit as a random number generator), and it is important to know how to avoid it.

All bistable cells have specific timing parameters (constraints) whose violation can lead to metastability. In this course, you will primarily work with bistable cells in the form of D flip-flops. For D flip-flops, these timing parameters are:

- T<sub>setup</sub> (**setup time**) — the interval during which the signal at input `D` must remain stable before the clock edge arrives.
- T<sub>hold</sub> (**hold time**) — the interval during which the signal at input `D` must remain stable after the clock edge arrives.

These two parameters define a timing window around the clock edge during which the input signal must remain stable. Violating these requirements leads to undefined flip-flop behaviour (see _fig. 9_). In the simplest case, the flip-flop will capture either the "old" or the "new" value that arrived at data input D in the vicinity of the clock edge, but which one is unknown. However, sometimes "the stars align" and the flip-flop enters a metastable state. The probability of this is extremely low (the kind of event described as "one in a billion"), yet it should not be dismissed. If a circuit operates at 1 GHz, the flip-flop updates its state one billion times per second, and the circuit itself may contain millions of flip-flops. In that context, "one in a billion" does not mean "nothing to worry about, it probably won't happen in my lifetime" — it means "damn, that's apparently why nothing works."

![../.pic/Introduction/Sequential%20logic/fig_09.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_09.drawio.svg)

_Figure 9. Example of D flip-flop timing parameter violations [[4](https://habr.com/ru/articles/254869/)]._

_Figure 9_ shows three possible outcomes of a timing violation:

1. Flip-flop output Q<sub>1</sub> captured the new value of signal D that was established within the T<sub>setup</sub> window.
2. Flip-flop output Q<sub>2</sub> captured the old value of signal D that was established before T<sub>setup</sub> began. On the next positive clock edge, input D already holds a settled value, which is captured without issue.
3. A signal transition during T<sub>setup</sub> caused a voltage equal to half the logic-high level to reach the flip-flop, pushing it into a metastable state. After some time the flip-flop settled into one of the stable states, but which one cannot be predicted in advance (shown as the hatched region where the flip-flop took either 0 or 1). On the next positive clock edge, input D already holds a settled value, which is captured without issue.

A T<sub>setup</sub> violation typically occurs when the circuit is clocked at a frequency incompatible with the circuit's critical path. The critical path is the combinational portion of the digital circuit with the greatest signal propagation delay. The propagation time along this path determines the minimum achievable clock period and, consequently, the maximum operating frequency of the entire circuit.

If the circuit is driven at a frequency that exceeds the constraint imposed by the critical path, the signal may not have settled at the end of the critical path, and if a flip-flop input is located there, its T<sub>setup</sub> constraint will be violated.

A T<sub>hold</sub> violation occurs when the circuit contains paths with a signal propagation delay to sequential logic elements that is shorter than the minimum permissible value. Such paths do not directly limit the maximum operating frequency, but they require the insertion of delay elements on the shortest paths. These paths are typically a significant concern in the design of application-specific integrated circuits (**ASICs**).

Suppose a circuit contains two registers A and B whose signal propagation delay is shorter than the minimum allowed. In this case, at the moment of the clock edge, a level transition may begin propagating from the output of register A. This transition reaches the input of register B within the same clock cycle, before B's T<sub>hold</sub> interval has expired.

To determine whether a circuit under design is capable of operating at the target frequency, **static timing analysis** (**STA**) is performed. During STA, the EDA tool calculates the propagation delays of all timing paths and identifies the critical path. The result of static timing analysis is the timing slack for each path when the circuit operates at the specified frequency. A positive slack indicates that the critical path delay is below the maximum allowed value, meaning the circuit frequency could potentially be increased (for example, by slightly reducing the supply voltage) by up to that margin. A negative slack indicates that the critical path delay already exceeds the allowed limit, and correct circuit operation requires either modifying the critical path to reduce its propagation delay or reducing the clock frequency.

Unfortunately, it is not always possible to meet flip-flop timing constraints, because in some cases the data input is inherently asynchronous (i.e., completely independent of the clock signal). For example, data may arrive at a flip-flop input from an external pin connected to a button press, which bears no relation to the clock. In other cases, data synchronized to one clock domain must be transferred to a region of the circuit operating from a different clock. This situation is called a **clock domain crossing** (**CDC**). Depending on the specific scenario, various synchronization circuits exist; the simplest is the insertion of an extra flip-flop at the point where a metastable state is anticipated (_fig. 10_). With high probability the synchronizing flip-flop output will settle to a valid state within 1–2 clock cycles. The uncertainty in the number of cycles arises because we do not know in which direction the first register in the chain will "fall".

![../.pic/Introduction/Sequential%20logic/fig_10.drawio.svg](../.pic/Introduction/Sequential%20logic/fig_10.drawio.svg)

_Figure 10. Circuit and timing diagram of the simplest synchronizer._

## Chapter Summary

1. Digital logic is divided into **combinational** and **sequential** logic.
   1. **Combinational** logic is memoryless logic whose outputs depend only on its inputs.
   2. **Sequential** logic is logic with memory whose outputs depend not only on its inputs but also on its internal state.
2. Digital circuits are also divided into **synchronous** and **asynchronous**.
   1. **Synchronous** circuits are sequential circuits whose state changes synchronously with the clock edge.
   2. **Asynchronous** circuits include both combinational circuits and sequential circuits whose state can change independently of the clock edge.
   3. Synchronous circuits with asynchronous preset/reset signals exist. In most cases they are treated as ordinary synchronous circuits, but their asynchronous preset/reset logic must be taken into account when calculating the **critical path**.
3. The **critical path** is the portion of a digital circuit with the greatest signal propagation delay along which no synchronous logic elements are encountered.
4. **Static memory** is a type of memory that retains data indefinitely as long as power is supplied, without requiring refresh cycles.
5. **Dynamic memory** is a type of memory that uses capacitors for storage, requiring periodic refresh of memory contents to prevent data loss.
6. The foundation of static memory is the **bistable cell**.
7. A **bistable cell** is an element capable of holding one of two stable states corresponding to the digital values "0" or "1".
8. The simplest bistable cell is a loop of two inverters. Its drawback is the absence of any means to write data from outside. This drawback is resolved by converting the circuit into an **RS latch**.
9. An **RS latch** is a bistable cell with two inputs: reset (R) and set (S). It can be built from a pair of NOR or NAND gates. The drawback of this bistable cell is the existence of a forbidden input combination that can lead to unpredictable behaviour. This drawback can be resolved by adding extra logic to obtain a **D latch**.
10. A **D latch** is a bistable cell with two inputs: a write-enable signal (`E` / `clk`) and a data input (D). While signal `E` is active, data from input `D` is stored in the D latch and appears at its output (the latch is said to be "transparent"). Although the D latch eliminates the forbidden state of the RS latch, it propagates all transients on the input signals for the entire time it is transparent.
11. A **D flip-flop** is a bistable cell that, like a D latch, has `clk` and `D` inputs, but captures data only at one of the clock edges (positive or negative). Like all bistable cells, the D flip-flop is susceptible to **metastability**. Metastability in a D flip-flop can occur if the data at input `D` changes within the timing window around the clock edge defined by the following two parameters:
    1. T<sub>setup</sub> (**setup time**) — the interval during which the input signal must remain stable before the clock edge arrives.
    2. T<sub>hold</sub> (**hold time**) — the interval during which the input signal must remain stable after the clock edge arrives.
12. The **metastable state** is a state of a bistable cell in which it is not in either stable digital state `0`/`1`, but instead sits approximately midway between them. After an indeterminate period of time (whose duration can only be estimated probabilistically), the bistable cell may exit this state and settle to either `0` or `1`.
13. In most cases metastability is an undesirable phenomenon in a digital circuit. It can be caused by operating the circuit at a frequency incompatible with the circuit's critical path. To determine whether the circuit can operate at a given frequency, **static timing analysis** (**STA**) is performed.
14. Metastability can also occur when the data signal is inherently asynchronous to the bistable cell's clock: it may be driven by external-world events or by bistable cells operating from different clocks (a situation called a **clock domain crossing**, **CDC**).

## References

1. D.M. Harris, S.L. Harris / Digital Design and Computer Architecture. RISC-V Edition, 2021;
2. Xilinx / [The Programmable Gate Array Data Book](https://archive.org/details/programmablegate00xili);
3. J. Wakerly, Digital Design: Principles and Practices (5th Edition). Pearson, 2017;
4. [Flip-flop metastability and clock domain synchronization](https://habr.com/ru/articles/254869/).
