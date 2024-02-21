/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Daniil Strelkov
* Email(s)       : @edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
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

    string str;

interrupt_controller dut(.*);
int err_count;

always #5 clk_i <= ~clk_i;

initial begin
  $display("\n\n===========================\n\nPress button 'Run All' (F3)\n\n===========================\n\n");
  $stop();
  clk_i       = '0;
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
  t13();
  t14();
  $display("Simulation finished. Number of errors: %d", err_count);
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
  $display("TEST 01. Granted request.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(1,0);
  @(posedge clk_i);
endtask

task t2();
  $display("TEST 02. Forbidden request.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 0;
  #1
  eror_info(0,0);
  @(posedge clk_i);
endtask

task t3();
  $display("TEST 03. Another request while handling previous.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);
endtask

task t4();
  $display("TEST 04. Request while unhandled exception.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);
endtask

task t5();
  $display("TEST 05. MRET while handling interrupt only.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  eror_info(0,1);
  @(posedge clk_i);
endtask

task t6();
  $display("TEST 06. MRET while handling exception only.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  eror_info(0,0);
  @(posedge clk_i);
endtask

task t7();
  $display("TEST 07. MRET while handling interrupt and exception.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i)
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  eror_info(0,0);
  @(posedge clk_i);
endtask

task t8();
  $display("TEST 08. Two MRETs while handling interrupt and exception.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
   @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  #1
  eror_info(0,1);
  @(posedge clk_i);
endtask

task t9();
  $display("TEST 09. MRET while unhandled interrupt and subsequent request.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(1,0);
  @(posedge clk_i);
endtask

task t10();
  $display("TEST 10. MRET while unhandled exception and subsequent request.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(1,0);
  @(posedge clk_i);
endtask

task t11();
  $display("TEST 11. MRET while unhandled interrupt and exception and subsequent request.");
  reset();
  @(posedge clk_i);
  mret_i      <= 0;
  exception_i <= 0;
  irq_req_i   <= 1;
  mie_i       <= 1;
  @(posedge clk_i);
  mret_i      <= 0;
  exception_i <= 1;
  irq_req_i   <= 0;
  mie_i       <= 1;
  @(posedge clk_i);
  mret_i      <= 1;
  exception_i <= 0;
  irq_req_i   <= 0;
  mie_i       <= 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);

endtask

task t12();
  $display("TEST 12. Two MRETs while unhandled interrupt and exception and susbsequent request.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 1;
  exception_i = 0;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  str = "request interrupt after 2 mret for interrupt and exception";
  eror_info(1,0);
  @(posedge clk_i);
endtask

task t13();
  $display("TEST 13. Request next cycle after excetion.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 0;
  mie_i       = 1;
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 0;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);
endtask

task t14();
  $display("TEST 14. Request same cycle with the exception.");
  reset();
  @(posedge clk_i);
  mret_i      = 0;
  exception_i = 1;
  irq_req_i   = 1;
  mie_i       = 1;
  #1
  eror_info(0,0);
  @(posedge clk_i);
endtask

//logic irq, irq_ret;

task eror_info(irq, irq_ret);
  if (irq_o!=irq)                 begin $error("invalid irq_o       = %b, expected value %b."           , irq_o, irq        ); err_count++; end
  if (irq_ret_o!=irq_ret)         begin $error("invalid irq_ret_o   = %b, expected value %b."           , irq_ret_o, irq_ret); err_count++; end
  if (irq_cause_o!=32'h1000_0010) begin $error("invalid irq_cause_o = %h, expected value 32'h1000_0010.", irq_cause_o       ); err_count++; end
endtask

endmodule
