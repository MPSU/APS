//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin

// Module Name:    tb_riscv_unit
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for peripheral units
//
//////////////////////////////////////////////////////////////////////////////////

module tb_riscv_unit();

logic clk;
logic ps2_clk;
logic ps2_dat;
logic resetn;
logic [15:0] sw_i;
logic [15:0] led_o;
logic parity;
logic starter;

logic [ 6:0] hex_led_o;
logic [ 7:0] hex_sel_o;
logic        rx_i;
logic        tx_o;

logic [3:0] cntr;

initial begin clk = 0; ps2_clk = 0; end

always #5 clk = ~clk;
always #50000 if(starter || (cntr > 0)) ps2_clk = ~ps2_clk; else ps2_clk = 1;

logic [11:0] data;

initial #5ms $finish();

initial begin
  resetn = 1;
  repeat(20)@(posedge clk);
  resetn = 0;
  repeat(20) @(posedge clk);
  resetn = 1;
end

riscv_unit dut(
  .clk_i    (clk      ),
  .resetn_i (resetn   ),
  .sw_i     (sw_i     ),
  .led_o    (led_o    ),
  .kclk_i   (ps2_clk  ),
  .kdata_i  (ps2_dat  ),
  .hex_led_o(hex_led_o),
  .hex_sel_o(hex_sel_o),
  .rx_i     (rx_i     ),
  .tx_o     (tx_o     )
);

initial begin: sw_block
  sw_i = 16'd0;
  repeat(260) @(posedge clk);
  sw_i = 16'hdead;
  repeat(300) @(posedge clk);
  sw_i = 16'h5555;
  repeat(300) @(posedge clk);
  sw_i = 16'hbeef;
  repeat(300) @(posedge clk);
  sw_i = 16'haaaa;
end


always @(negedge ps2_clk) begin: ps2_always_block
  if(starter || (cntr > 0))
    if(cntr == 10)
      cntr <= 0;
    else
      cntr <= cntr + 1;
end

assign ps2_dat = cntr>0? data[cntr-1] : 1;

initial begin: ps2_initial_block
  cntr = 0;
  starter = 0;
  data = 0;
  #100000;
  ps2_send_scan_code(8'h1c);
  ps2_send_scan_code(8'he0);
  ps2_send_scan_code(8'hf0);
  ps2_send_scan_code(8'h1c);
  ps2_send_scan_code(8'h5c);
end

task ps2_send_scan_code(input logic [7:0] code);
  data = {2'b11, !(^code), code, 1'b0};
  starter = 1;
  @(posedge ps2_clk);
  starter = 0;
  repeat(10) @(posedge ps2_clk);
endtask


// TODO uart block


endmodule
