/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_16_tb_coremark();
  import bluster_pkg::*;
  logic        clk100mhz_i;
  logic        aresetn_i;
  logic        rx_i;
  logic        tx_o;
  logic        clk_i;
  logic        rst_i;
  logic        core_reset;
  assign aresetn_i = !rst_i;
  assign core_reset = DUT.core.rst_i;
  logic rx_busy, rx_valid, tx_busy, tx_valid;
  logic [7:0] rx_data, tx_data;

  always #50ns clk_i = !clk_i;
  always #5ns clk100mhz_i = !clk100mhz_i;

  byte coremark_msg[103];
  integer coremark_cntr;

  initial begin
    $timeformat(-9, 2, " ns", 3);
    clk100mhz_i = 0;
    clk_i = 0;
    rst_i <= 0;
    @(posedge clk_i);
    rst_i <= 1;
    repeat(2) @(posedge clk_i);
    rst_i <= 0;

    finish_programming(clk_i, tx_valid, tx_busy, core_reset, tx_data);

    coremark_cntr = 0;
    coremark_msg = {32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32};
    forever begin
      @(posedge clk_i);
      if(rx_valid) begin
        if((rx_data == 10) | (rx_data == 13)) begin
          $display("%s", coremark_msg);
          coremark_cntr = 0;
          coremark_msg = {32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32};
        end
        else begin
          coremark_msg[coremark_cntr] = rx_data;
          coremark_cntr++;
        end
      end
    end
  end

  initial #500ms $finish();
  processor_system DUT(
    .clk_i      (clk100mhz_i), 
    .resetn_i   (aresetn_i), 
    .rx_i       (rx_i), 
    .tx_o       (tx_o)
);

  uart_rx rx(
  .clk_i      (clk_i      ),
  .rst_i      (rst_i      ),
  .rx_i       (tx_o       ),
  .busy_o     (rx_busy    ),
  .baudrate_i (17'd115200 ),
  .parity_en_i(1'b1       ),
  .stopbit_i  (1'b1       ),
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
  .stopbit_i  (1'b1       ),
  .tx_data_i  (tx_data    ),
  .tx_valid_i (tx_valid   )
);

endmodule
