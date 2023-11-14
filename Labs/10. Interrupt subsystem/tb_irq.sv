//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Daniil Strelkov

// Module Name:    tb_irq
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for interrupt controller
//
//////////////////////////////////////////////////////////////////////////////////


module tb_irq();
    logic     clk_i;
    logic     rst_i;
    logic     exception_i;
    logic     irq_req_i;
    logic     mret_i;
    logic     mie_i;

    logic        irq_ret_o;
    logic [31:0] irq_cause_o;
    logic        irq_o;

interrupt_controller dut(.*);

always #5 clk_i <= ~clk_i;

initial begin
  $display("\n\n===========================\n\nPress button 'Run All' (F3)\n\n===========================\n\n");
  $stop();
  clk_i <= 0;
  exception_i = '0;
  mret_i      = '0;
  irq_req_i   = '0;
  mie_i       = '0;
  repeat(4)@(posedge clk_i);
  t1();
  t2();
  t3();
  t4();
  t5();
  t6();
  t7();
  t8();
  t9();
  t10();
  t11();
  t12();
  $finish;
end

task reset();
rst_i <= 1'b1;
@(posedge clk_i);
@(posedge clk_i);
rst_i <= 1'b0;
mret_i      = 0;
exception_i = 0;
irq_req_i   = 0;
mie_i       = 0;
endtask
logic [1:0] k;

task t1();  
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=1) $display("Error: irq_o != 1");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);
endtask

task t2();
  reset();
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 0;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
endtask

task t3();
  reset();
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
endtask

task t4();
  reset();
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
endtask

task t5();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=1) $display("Error: irq_ret_o != 1");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
endtask

task t6();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
endtask

task t7();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);
endtask

task t8();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=1) $display("Error: irq_ret_o != 1");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);

endtask

task t9();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=1) $display("Error: irq_ret_o != 1");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=1) $display("Error: irq_o != 1");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
endtask

task t10();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=1) $display("Error: irq_o != 1");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
endtask

task t11();
  reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
endtask

task t12();
 reset();
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 1;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
@(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
  @(posedge clk_i);
  mret_i        = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  if (irq_o!=0) $display("Error: irq_o != 0");
  if (irq_ret_o!=1) $display("Error: irq_ret_o != 1");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
@(posedge clk_i);
  mret_i        = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  if (irq_o!=1) $display("Error: irq_o != 1");
  if (irq_ret_o!=0) $display("Error: irq_ret_o != 0");
  if (irq_cause_o!=32'h1000_0010) $display("Error: irq_o != 32'h1000_0010");
endtask

endmodule
