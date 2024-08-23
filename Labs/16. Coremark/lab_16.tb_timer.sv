/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_16_tb_timer();

  logic        clk_i;
  logic        rst_i;
  logic        req_i;
  logic        write_enable_i;
  logic [31:0] addr_i;
  logic [31:0] write_data_i;
  logic [31:0] read_data_o;
  logic        ready_o;
  logic        interrupt_request_o;

localparam SYS_CNT_ADDR = 32'h0000_0000;
localparam DELAY_ADDR   = 32'h0000_0008;
localparam MODE_ADDR    = 32'h0000_0010;
localparam REP_CNT_ADDR = 32'h0000_0014;
localparam RST_ADDR     = 32'h0000_0024;

localparam OFF      = 32'd0;
localparam NTIMES   = 32'd1;
localparam FOREVER  = 32'd2;

always #50ns clk_i = !clk_i;

timer_sb_ctrl DUT(.*);

initial begin
  clk_i = 0;
  rst_i = 0;
  req_i = 0;
  write_enable_i = 0;
  addr_i = 0;
  write_data_i = 0;
  @(posedge clk_i);
  rst_i = 1;
  repeat(5) @(posedge clk_i);
  rst_i = 0;

  test_ntimes(0, 0);
  test_ntimes(0, 1);
  test_ntimes(1, 0);
  test_ntimes(1, 1);
  test_ntimes(10, 1);
  test_ntimes(10, 10);
  test_forever(10);
  write_req(MODE_ADDR, OFF);
  test_ntimes(10, 10);
  test_forever(10);
  test_ntimes(10, 10);
  $finish();
end

one_cycle_irq: assert property (
  @(posedge clk_i) disable iff ( rst_i || (DUT.delay==32'd1))
  (interrupt_request_o |=> !interrupt_request_o)
);

task test_ntimes(input logic [31:0] delay, ntimes);
  write_req(DELAY_ADDR, delay);
  write_req(REP_CNT_ADDR, ntimes);
  write_req(MODE_ADDR, NTIMES);
  repeat(ntimes) begin
    repeat(delay)@(posedge clk_i);
    if(!interrupt_request_o & delay) begin
      $error("test_ntimes: delay = %d, ntimes = %d", delay, ntimes);
    end
  end
endtask

task test_forever(input logic [31:0] delay);
  write_req(DELAY_ADDR, delay);
  write_req(MODE_ADDR, FOREVER);
  repeat(1000) begin
    repeat(delay) @(posedge clk_i);
    if(!interrupt_request_o) begin
      $error("test_forever");
    end
  end
endtask

task write_req(input [31:0] addr, data);
  @(posedge clk_i);
  addr_i <= addr;
  write_data_i <= data;
  write_enable_i <= 1'b1;
  req_i <= 1'b1;
  @(posedge clk_i);
  while(!ready_o) begin
    @(posedge clk_i);
  end
  req_i <= 1'b0;
  write_enable_i <= 1'b0;
endtask

endmodule