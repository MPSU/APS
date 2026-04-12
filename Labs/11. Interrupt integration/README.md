# Lab 11. Interrupt Subsystem Integration

After implementing the interrupt subsystem, it must be integrated into the processor system. To do this, update the `processor_core` module according to the diagram shown in _Fig. 1_:

![../../.pic/Labs/lab_11_irq_integration/fig_01.drawio.svg](../../.pic/Labs/lab_11_irq_integration/fig_01.drawio.svg)

_Figure 1. Integration of the interrupt subsystem into the processor core._

<details>
<summary>Diagram without highlighting new parts relative to the previous module version</summary>

![../../.pic/Labs/lab_10_irq/fig_03.drawio.svg](../../.pic/Labs/lab_10_irq/fig_03.drawio.svg)

_Figure 2. Diagram without highlighting new parts relative to the previous module version._

</details>

## Assignment

Integrate the `csr_controller` and `interrupt_controller` modules into the `processor_core` module. The `processor_core` module will have an updated interface (due to the addition of `irq_req_i` input and `irq_ret_o` output):

```Verilog
module processor_core (
  input  logic        clk_i,
  input  logic        rst_i,

  input  logic        stall_i,
  input  logic [31:0] instr_i,
  input  logic [31:0] mem_rd_i,
  input  logic        irq_req_i,

  output logic [31:0] instr_addr_o,
  output logic [31:0] mem_addr_o,
  output logic [ 2:0] mem_size_o,
  output logic        mem_req_o,
  output logic        mem_we_o,
  output logic [31:0] mem_wd_o,
  output logic        irq_ret_o
);
```

Update the instantiation of the `processor_core` module in the `processor_system` module to account for the new ports. Create wires `irq_req` and `irq_ret` and connect them to the corresponding inputs/outputs of `processor_core`. The other ends of these wires will not yet be connected to anything — this will change in [Lab 13](../13.%20Peripheral%20units/).

If you want to extend the number of interrupt sources, you may complete the optional [Lab 12](../12.%20Daisy%20chain).

### Steps

1. Replace the `program.mem` file in the `Design Sources` of the project with the new file [program.mem](program.mem) provided in this lab. This file contains the program from _Listing 1_ of Lab 10.
2. Integrate the `csr_controller` and `interrupt_controller` modules into the `processor_core` module.
   1. Note that the `processor_core` module now includes new input and output signals: `irq_req_i` and `irq_ret_o`. These ports must be used when instantiating `processor_core` in the `processor_system` module.
      1. Connect the `irq_req` wire to the `irq_req_i` input; the other end of this wire will remain unconnected for now.
      2. Connect the `irq_ret` wire to the `irq_ret_o` output; it will also remain unused for now.
      3. The wire names `irq_req` and `irq_ret` must be exactly as specified, as they are used by the verification environment for this lab.
   2. Note the appearance of the `imm_Z` constant — it is the only core constant that is zero-extended rather than sign-extended.
3. Verify the module using the verification environment provided in the file [lab_11.tb_processor_system.sv](lab_11.tb_processor_system.sv).
   1. Before running the simulation, make sure that the correct top-level module is selected in `Simulation Sources`.
   2. As with verification of the CYBERcobra processor architecture, you will not be explicitly told whether the test passed or failed. You must manually, cycle by cycle, verify that the processor correctly executes the instructions described in [Listing 1](../10.%20Interrupt%20subsystem#Пример-обработки-перехвата) of Lab 10 (see the procedure of Lab 4). To do this, first determine what each instruction should do, then check that the processor performs exactly that.
4. This laboratory work does not require FPGA validation.
