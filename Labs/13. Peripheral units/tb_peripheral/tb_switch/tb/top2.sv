`include "../interface.sv"
module tb_sw();


  parameter [31:0] ADDR_DATA = 32'h0;

  logic        clk_i;  
  logic        resetn_i;

  int          err_count;
  

  logic [15:0] sw_i; 
  logic [31:0] addr;

  static bit   test_finished;
  peripheral_if sw_if(clk_i);

  event sw_reset_begin;
  event sw_reset_end;

  sw_sb_ctrl sw(
      .rst_i              (resetn_i                  ),
      .clk_i              (clk_i                     ),
      .req_i              (sw_if.req_i               ),
      .write_enable_i     (sw_if.write_enable_i      ),
      .addr_i             (sw_if.addr_i              ),
      .write_data_i       (sw_if.write_data_i        ),
      .read_data_o        (sw_if.read_data_o         ),
      .sw_i               (sw_i                      ),
      .interrupt_request_o(sw_if.interrupt_request_o ),
      .interrupt_return_i (sw_if.interrupt_return_i  ),
      .ready_o            (sw_if.ready_o             )
    );

sequence read_request;
  (sw_if.req_i && !sw_if.write_enable_i && (sw_if.addr_i == ADDR_DATA));
endsequence

sequence write_request;
  (sw_if.req_i && sw_if.write_enable_i && (sw_if.addr_i == ADDR_DATA));
endsequence


property check_read_data_o_without_access_read;
 @(posedge clk_i) (!sw_if.req_i && !sw_if.write_enable_i && sw_if.addr_i == ADDR_DATA) |=> $stable(sw_if.read_data_o);
endproperty

assert property (check_read_data_o_without_access_read) else begin
  $error(" read_data_o changed without read access. Expected: %0h, Got: %0h, at Time: %0t.",
         $past(sw_if.read_data_o, 1), sw_if.read_data_o, $realtime);
end

property check_read_data_o_reset;
  @(posedge clk_i) 
  sw_if.req_i && !sw_if.write_enable_i && (sw_if.addr_i == ADDR_DATA) && resetn_i |=> (sw_if.read_data_o == 32'b0);
endproperty

assert property (check_read_data_o_reset) else begin
  $error("Invalid value read_data_o for read request with reset enabled. Expected output data: %0h, Got: %0h, at Time: %0t.",
         32'b0, sw_if.read_data_o, $realtime);
end

property check_read_data_o_read;
  @(posedge clk_i) disable iff (resetn_i)  
  read_request |=> (sw_if.read_data_o == {16'b0, sw_i});
endproperty

assert property (check_read_data_o_read) else begin 
  $error(" read_data_o when read_request is called Expected: %0h, Got: %0h, at Time: %0t", sw_i, sw_if.read_data_o, $realtime); err_count++; end


property check_read_data_o_write;
  @(posedge clk_i) (sw_if.write_enable_i) |=> ($stable(sw_if.read_data_o));
endproperty

assert property (check_read_data_o_write) else begin
  $error("Read data output changed after a write request. Expected: %0h, Got: %0h, at Time: %0t.", $past(sw_if.read_data_o , 1), sw_if.read_data_o, $realtime); err_count++; end


property check_read_data_o_not_work_addr;
  @(posedge clk_i)
  (sw_if.req_i && !sw_if.write_enable_i && (sw_if.addr_i != ADDR_DATA)) |=> ($stable(sw_if.read_data_o));
endproperty

assert property (check_read_data_o_not_work_addr) else begin 
  $error(" read_data_o when read_request is called at not working address  Expected: %0h, Got: %0h, at Time: %0t", $past(sw_if.read_data_o , 1), sw_if.read_data_o, $realtime); err_count++; end


property check_interrupt_request;
  @(posedge clk_i) ((sw_i !== $past(sw_i) && !resetn_i)) |=> (sw_if.interrupt_request_o === 1'b1);
endproperty

assert property (check_interrupt_request) else begin
  $error("interrupt_request_o was not asserted when sw_i changed at Time: %0t.", $realtime); err_count++; end


property interrupt_request_stability;
    @(posedge clk_i) (((sw_i == $past(sw_i)) || ( !sw_if.interrupt_return_i)) && !resetn_i) |=>  $stable(sw_if.interrupt_request_o);
endproperty

// assert property (interrupt_request_stability) else begin
//   $error(" Interrupt request output should have remained stable, but changed unexpectedly. Expected: %0b, Got: %0b at Time: %0t.",
//          $past(sw_if.interrupt_request_o, 1), sw_if.interrupt_request_o, $realtime); err_count++;
// end


property p_interrupt_hold;
@(posedge clk_i) sw_if.interrupt_request_o == 1 |-> ##[0:$] (sw_if.interrupt_request_o == 1) until_with (sw_if.interrupt_return_i == 1);
endproperty

assert property (p_interrupt_hold) else begin
  $error(" Interrupt request must hold at 1 until interrupt return is received Expected: %0h, Got: %0h, at Time: %0t.", 1, sw_if.interrupt_request_o, $realtime); err_count++; end


property maintain_interrupt_request;
  @(posedge clk_i)
    (sw_if.interrupt_request_o && $fell(sw_if.interrupt_return_i) && !resetn_i) |=> (sw_if.interrupt_request_o == 0);
endproperty

assert property (maintain_interrupt_request) else begin
  $error("Interrupt request did not deassert after interrupt return fell. Expected: %0h, Got: %0h, at Time: %0t.", 0, sw_if.interrupt_request_o, $realtime); err_count++; end


property maintain_interrupt_request_rst;
  @(posedge clk_i)
    (sw_if.interrupt_request_o && resetn_i) |=> (sw_if.interrupt_request_o == 0);
endproperty

assert property (maintain_interrupt_request_rst) else begin
  $error("Interrupt request was not deasserted on reset. Expected: %0h, Got: %0h, at Time: %0t.", 0, sw_if.interrupt_request_o, $realtime); err_count++; end


property reset_interrupt_on_return_and_reset;
  @(posedge clk_i)
    (sw_if.interrupt_return_i && resetn_i) |=> (sw_if.interrupt_request_o == 0);
endproperty

assert property (reset_interrupt_on_return_and_reset) else begin
  $error("Interrupt request was not reset after interrupt return and reset were high. Expected: %0h, Got: %0h, at Time: %0t.", 0, sw_if.interrupt_request_o, $realtime); err_count++; end

 

  task sw_read_test();
  
    repeat (5) begin
  
      @(posedge clk_i);
  
      sw_i <= $random;
  
      sw_if.read_request(ADDR_DATA);

      @(posedge clk_i);

      sw_if.interrupt_return();
    end
  endtask



  task sw_reset_test();
 
    ->sw_reset_begin;
  
    repeat(2)
      @(posedge clk_i);
  
    sw_if.read_request(32'h0);
 
    @(posedge clk_i);
  
    sw_if.interrupt_return();
  
    @(posedge clk_i);

    sw_if.write_request(32'b0, $urandom_range(16'hFFFF, 0));

    repeat(2)
      @(posedge clk_i);

    ->sw_reset_end;

    sw_if.interrupt_return();
  endtask


  task sw_read_without_access();
  
    repeat (3) begin
  
      @(posedge clk_i);
  
      sw_i <= $random;

      @(posedge clk_i);
  
      sw_if.read_without_access(32'b0);
    
      @(posedge clk_i);
    
      sw_if.interrupt_return();
    end
  
  endtask

  task sw_write_test();

    repeat(3) begin
      @(posedge clk_i);
  
      sw_i <= $random;
  
      @(posedge clk_i);
    
      sw_if.write_request(32'b0, $urandom_range(16'hFFFF, 0));
  
      @(posedge clk_i);
    
      sw_if.interrupt_return();
    end
  
  endtask

task sw_write_without_access();

  repeat (5) begin

    @(posedge clk_i);
  
    sw_i <= $random;
  
    @(posedge clk_i);
  
    sw_if.write_without_access(32'b0, $urandom_range(16'hFFFF, 0));
  
    @(posedge clk_i);
    
    sw_if.interrupt_return();
  end


endtask

initial begin
  $timeformat(-9, 3, "ns", 8);

  err_count = 0;
  repeat(2)
    @(posedge clk_i);

  sw_read_test();
  sw_write_test();
  sw_write_without_access();
  sw_reset_test();

  sw_read_without_access();

  test_finished = 1;
end



initial begin
  clk_i = 0;
  forever #5 clk_i = ~clk_i;
end

initial begin
  resetn_i = 1;

  @(posedge clk_i);
  
  sw_i = 16'd0;

  @(posedge clk_i);

  resetn_i = 0;

  @sw_reset_begin;
  resetn_i = 1;

  @sw_reset_end;
  resetn_i = 0;

end

always  @(posedge clk_i)  begin
  if (test_finished) begin
    $display("All tests finished, number of errors: %0d", err_count);
    $finish; end 
end


always  @(posedge clk_i)  begin
  if (err_count > 10) begin
    $display("More than 10 errors");
    $fatal; end 
end
endmodule