/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_15_tb_system();

  logic          clk_i;
  logic          sysclk;
  logic          rst_i;
  logic          flash_rx;
  logic          tx_o;
  logic ps2_clk, ps2_dat;
  logic sw_i;
  logic tb_rx;
  logic flashing_is_done = 0;
  logic core_reset;

  logic rx_busy, rx_valid, tx_busy, tx_valid;
  logic [7:0] rx_data, tx_data;

  import bluster_pkg::*;
  import peripheral_pkg::*;

  byte init_str[INIT_MSG_SIZE];
  byte done_str[FLASH_MSG_SIZE];

  always #5ns clk_i = !clk_i;
  always #50ns sysclk = !sysclk;

  initial begin
    $timeformat(-9, 2, " ns", 3);
    sysclk = 0;
    clk_i = 0;
    rst_i <= 0;
    @(posedge sysclk);
    rst_i <= 1;
    repeat(2) @(posedge sysclk);
    rst_i <= 0;
    program_region("YOUR_INSTR_MEM_FILE.mem", sysclk, tx_valid, rx_valid, tx_o, tx_busy, core_reset, rx_data, tx_data);
    program_region("YOUR_DATA_MEM_FILE.mem", sysclk, tx_valid, rx_valid, tx_o, tx_busy, core_reset, rx_data, tx_data);
    finish_programming(sysclk, tx_valid, tx_busy, core_reset, tx_data);
    repeat(200) @(posedge sysclk);
    flashing_is_done = 1;
    #4ms;
    $finish();
  end

  initial begin: sw_block
    sw_i = 16'd0;
    wait(flashing_is_done);
    sw_i = 16'hdead;
    repeat(1000) @(posedge clk_i);
    sw_i = 16'h5555;
    repeat(1000) @(posedge clk_i);
    sw_i = 16'hbeef;
    repeat(1000) @(posedge clk_i);
    sw_i = 16'haaaa;
  end

  initial begin: ps2_initial_block
    ps2_clk = 1'b1;
    ps2_dat = 1'b1;
    wait(flashing_is_done);
    ps2_send_scan_code(8'h1C, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'hf0, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'h1C, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'h32, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'hf0, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'h32, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'h21, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'hf0, ps2_clk, ps2_dat);
    repeat(1000) @(posedge clk_i);
    ps2_send_scan_code(8'h21, ps2_clk, ps2_dat);
  end

  initial begin: uart_rx_initial_block
    tb_rx = 1'b1;
    wait(flashing_is_done);
    uart_rx_send_char(8'h1c, 115200, tb_rx);
    repeat(1000) @(posedge clk_i);
    uart_rx_send_char(8'h0D, 115200, tb_rx);
    repeat(1000) @(posedge clk_i);
    uart_rx_send_char(8'h0D, 115200, tb_rx);
    repeat(1000) @(posedge clk_i);
    uart_rx_send_char(8'h7F, 115200, tb_rx);
    repeat(1000) @(posedge clk_i);
    uart_rx_send_char(8'h7F, 115200, tb_rx);
  end


  system dut(
    .clk_i    (clk_i  ),
    .resetn_i (!rst_i ),
    .rx_i     (flashing_is_done ? tb_rx : flash_rx ),
    .tx_o     (tx_o   ),
    .kclk_i   (ps2_clk),
    .kdata_i  (ps2_dat),
    .sw_i     (sw_i   )
  );

  assign core_reset = dut.core_inst.rst_i;

  uart_rx rx(
  .clk_i      (sysclk     ),
  .rst_i      (rst_i      ),
  .rx_i       (tx_o       ),
  .busy_o     (rx_busy    ),
  .baudrate_i (17'd115200 ),
  .parity_en_i(1'b1       ),
  .stopbit_i  (2'b1       ),
  .rx_data_o  (rx_data    ),
  .rx_valid_o (rx_valid   )
  );

  uart_tx tx(
    .clk_i      (sysclk     ),
    .rst_i      (rst_i      ),
    .tx_o       (flash_rx   ),
    .busy_o     (tx_busy    ),
    .baudrate_i (17'd115200 ),
    .parity_en_i(1'b1       ),
    .stopbit_i  (2'b1       ),
    .tx_data_i  (tx_data    ),
    .tx_valid_i (tx_valid   )
  );

endmodule
