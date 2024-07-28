/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
package peripheral_pkg;

  localparam DMEM_ADDR_HIGH   = 8'h00;
  localparam SW_ADDR_HIGH     = 8'h01;
  localparam LED_ADDR_HIGH    = 8'h02;
  localparam PS2_ADDR_HIGH    = 8'h03;
  localparam HEX_ADDR_HIGH    = 8'h04;
  localparam RX_ADDR_HIGH     = 8'h05;
  localparam TX_ADDR_HIGH     = 8'h06;
  localparam VGA_ADDR_HIGH    = 8'h07;
  localparam TIMER_ADDR_HIGH  = 8'h08;

  task automatic ps2_send_scan_code(input logic [7:0] code, ref logic ps2_clk, ref logic ps2_dat);
    logic [11:0] data = {2'b11, !(^code), code, 1'b0};
    for(int i = 0; i < 11; i++) begin
      ps2_dat = data[i];
      #15us;
      ps2_clk = 1'b0;
      #15us;
      ps2_clk = 1'b1;
    end
  endtask

  task automatic uart_rx_send_char(input logic [7:0] char, input logic [31:0] baudrate, ref logic tx);
    logic [11:0] data = {2'b11, (^char), char, 1'b0};
    for(int i = 0; i < 12; i++) begin
      tx = data[i];
      #(1s/baudrate);
    end
  endtask

endpackage