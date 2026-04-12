# Testing the Register File on FPGA

After verifying the register file in simulation, you need to test it on an FPGA prototype.

Instructions for implementing the prototype are described [here](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

_Fig. 1_ shows the prototype schematic on the FPGA.

![../../../.pic/Labs/board%20files/nexys_rf_riscv_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_structure.drawio.svg)

_Figure 1. Block diagram of the `nexys_rf_riscv` module._

## Peripheral Description

The peripherals are shown in _Fig. 2_.

![../../../.pic/Labs/board%20files/nexys_rf_riscv_control.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_control.drawio.svg)

_Figure 2. Peripherals available to the prototype._

-   ### Switches and Buttons

    Working with the register file requires setting address and data signals.
    The board does not have enough switches for all register file inputs, so addresses and data are provided from a single input source:

    1.  **Address** inputs (`read_addr1_i` / `read_addr2_i` / `write_addr_i`) of the register file are set via switches `SW[14:0]` as follows:

        -   `SW[ 4: 0]` — `write_addr_i`
        -   `SW[ 9: 5]` — `read_addr2_i`
        -   `SW[14:10]` — `read_addr1_i`

        To latch the entered addresses onto the register file input ports, press button `BTND` (`addr_en` in _Fig. 2_). This stores the addresses in a memory element.

    1.  **Data** input (`write_data_i`) of the register file is set via switches `SW[15:0]`. Only the lower 16 bits of data can be entered this way. To write the entered data to the `write_addr_i` address, press button `BTNR` (`we` in _Fig. 2_).

-   ### LEDs

    LEDs `LED[14:0]` display the addresses (`read_addr1_i` / `read_addr2_i` / `write_addr_i`) currently set on the register file ports:

    -   `LED[ 4: 0]` — `write_addr_i`
    -   `LED[ 9: 5]` — `read_addr2_i`
    -   `LED[14:10]` — `read_addr1_i`

-   ### Seven-Segment Displays

    The left block of seven-segment displays (displays 7–4) shows the lower 16 bits of port `read_data1_o`, and the right block (displays 3–0) shows the lower 16 bits of port `read_data2_o`.

    Numbers are displayed in **hexadecimal** format.

## Performing Register File Operations on the Prototype

Available operations: write, read.

-   ### Write

    The following example walks through the steps required to write to the register file.

    1.  Write the value `0x1234` to register `5`.

        1.  Immediately after programming, as indicated by the unlit LEDs, all register file ports have zero addresses. We need to change the write address, so set the switches to `5` and press button `BTND` (see _Fig. 3_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_5.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_5.drawio.svg)

            _Figure 3. Setting address `5` on the `write_addr_i` port of the register file._

            Note: the LEDs immediately display address `5` after the button is pressed.

        1.  To write data to the specified (fifth) register, set the switches to `0x1234` and press button `BTNR` (see _Fig. 4_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_1234.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_1234.drawio.svg)

            _Figure 4. Writing `0x1234` to register `5`._

    1.  Write the value `0x5678` to register `6`.

        1.  Set the write-address switches to `6` and press button `BTND` (see _Fig. 5_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_6.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_6.drawio.svg)

            _Figure 5. Setting address `6` on the `write_addr_i` port of the register file._

            Note: the LEDs immediately display address `6` after the button is pressed.

        1.  To write data to the specified (sixth) register, set the switches to `0x5678` and press button `BTNR` (see _Fig. 6_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_5678.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_5678.drawio.svg)

            _Figure 6. Writing `0x5678` to register `6`._

-   ### Read

    The following example walks through the steps required to read from the register file. We will read the previously written values `0x1234` and `0x5678` from registers `5` and `6` respectively, and display them on both seven-segment display blocks (7–4 and 3–0).

    Set value `5` and `6` on the `ra1` and `ra2` switch groups (see _Fig. 2_) respectively, then press button `BTND` to update the address with the switch values (see _Fig. 7_).

    ![../../../.pic/Labs/board%20files/nexys_rf_riscv_read.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_read.drawio.svg)

    _Figure 7. Reading from registers `5` and `6`._

    Note that for a read operation, it is sufficient to set the desired address on the register file port — the register contents are immediately available on the output.

> [!NOTE]
> The `CPU_RESETN` reset button does not clear the contents of the register file, because the reset signal is not connected to the register file module, and the `nexys_rf_riscv` module does not reset it independently. To reset, you can reprogram the FPGA.

Try writing data to register zero, then to other addresses. Then read back the written data and verify that it matches what you wrote (taking into account the special behavior of the RISC-V register file).
