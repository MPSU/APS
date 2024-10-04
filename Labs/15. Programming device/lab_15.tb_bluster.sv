/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_15_tb_bluster();

  logic          clk_i;
  logic          rst_i;
  logic          rx_i;
  logic          tx_o;
  logic [ 31:0]  instr_addr_o;
  logic [ 31:0]  instr_wdata_o;
  logic          instr_we_o;
  logic [ 31:0]  data_addr_o;
  logic [ 31:0]  data_wdata_o;
  logic          data_we_o;
  logic          core_reset_o;

  logic rx_busy, rx_valid, tx_busy, tx_valid;
  logic [7:0] rx_data, tx_data;

  logic [31:0]   instr_addr_i;
  logic [31:0]   instr_rdata_o;

  import bluster_pkg::*;

  byte init_str[INIT_MSG_SIZE];
  byte done_str[FLASH_MSG_SIZE];

  always #50ns clk_i = !clk_i;

  initial begin
    $timeformat(-9, 2, " ns", 3);
    clk_i = 0;
    rst_i <= 0;
    @(posedge clk_i);
    rst_i <= 1;
    repeat(2) @(posedge clk_i);
    rst_i <= 0;
    program_region("lab_15_instr.mem", clk_i, tx_valid, rx_valid, tx_o, tx_busy, core_reset_o, rx_data, tx_data);
    program_region("lab_15_data.mem", clk_i, tx_valid, rx_valid, tx_o, tx_busy, core_reset_o, rx_data, tx_data);
    program_region("lab_15_char.mem", clk_i, tx_valid, rx_valid, tx_o, tx_busy, core_reset_o, rx_data, tx_data);
    finish_programming(clk_i, tx_valid, tx_busy, core_reset_o, tx_data);
    $finish();
  end


  bluster DUT(.*);

  uart_rx rx(
  .clk_i      (clk_i      ),
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
    .clk_i      (clk_i      ),
    .rst_i      (rst_i      ),
    .tx_o       (rx_i       ),
    .busy_o     (tx_busy    ),
    .baudrate_i (17'd115200 ),
    .parity_en_i(1'b1       ),
    .stopbit_i  (2'b1       ),
    .tx_data_i  (tx_data    ),
    .tx_valid_i (tx_valid   )
  );

  rw_instr_mem imem(
    .clk_i         (clk_i               ) ,
    .read_addr_i   (instr_addr_i        ) ,
    .read_data_o   (instr_rdata_o       ) ,
    .write_addr_i  (instr_addr_o        ) ,
    .write_data_i  (instr_wdata_o       ) ,
    .write_enable_i(instr_we_o          )
  );

  data_mem dmem(
    .clk_i          (clk_i                  ),
    .mem_req_i      (data_addr_o[31:24] == 0),
    .write_enable_i (data_we_o              ),
    .byte_enable_i  (4'b1111                ),
    .addr_i         (data_addr_o            ),
    .write_data_i   (data_wdata_o           ),
    .read_data_o    (),
    .ready_o        ()
  );

  data_mem cmem(
    .clk_i          (clk_i                  ),
    .mem_req_i      (data_addr_o[31:24] == 7),
    .write_enable_i (data_we_o              ),
    .byte_enable_i  (4'b1111                ),
    .addr_i         (data_addr_o            ),
    .write_data_i   (data_wdata_o           ),
    .read_data_o    (),
    .ready_o        ()
  );

endmodule
