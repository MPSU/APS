# Lab 9. Integration of the Load/Store Unit

After implementing the load/store unit, it must be integrated into the processor system developed in Lab 7. Figure 1 shows a diagram illustrating the integration of components:

![../../.pic/Labs/lab_08_lsu/fig_01.drawio.svg](../../.pic/Labs/lab_08_lsu/fig_01.drawio.svg)

_Figure 1. Connecting the LSU to the processor system._

## Preparation Materials

Before performing this lab, it is recommended to study the theoretical part of Lab #8.

## Assignment

Integrate the `lsu` module into the `processor_system` module.

### Steps

1. Integrate the `lsu` and `data_mem` modules into the `processor_system` module.
   1. Note that the `stall` signal logic must be removed from the `processor_system` module, since it has been moved inside the `lsu` module.
2. After integration, verify the processor system using the [program](../07.%20Datapath/#Assignment) and verification environment from Lab 7.
   1. As with testing the CYBERcobra architecture processor, you will not be explicitly told whether the test passed. You need to manually check, cycle by cycle, that the processor correctly executes the instructions described in [_Listing 1_](../07.%20Datapath/#Assignment) of Lab 7 (see the procedure in Lab #4). To do this, first determine yourself what each instruction should do, and then verify that the processor does exactly that.
   2. Pay attention to how the instructions `sw`, `sh`, `sb`, `lw`, `lh`, `lb`, `lhu`, `lbu` are executed now.
3. This lab does not require testing on FPGA.
