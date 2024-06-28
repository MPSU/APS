`include "../interface.sv"
module tb_leds();

  parameter [31:0] ADDR_LED_VAL  = 32'b0;
  parameter [31:0] ADDR_LED_MODE = 32'h04;
  parameter [31:0] ADDR_LED_RST  = 32'h024;
  parameter [31:0] MAX_LED_VAL  = 65535;


  logic        clk_i;  
  logic        resetn_i;
  
  logic [15:0] led_o; 


  int err_count;

  logic [31:0] addr;
  logic [31:0] last_led_o;
  logic [31:0] last_read_data_o;


  peripheral_if led_if(clk_i);
  static bit   test_finished;

  static logic [31:0] address_list[3] = {ADDR_LED_VAL, ADDR_LED_RST, ADDR_LED_MODE};

  typedef enum {READ, WRITE} access_type_t;

  event leds_reset_begin;
  event leds_reset_end;

  led_sb_ctrl leds(
      .rst_i              (resetn_i                  ),
      .clk_i              (clk_i                     ),
      .req_i              (led_if.req_i               ),
      .write_enable_i     (led_if.write_enable_i      ),
      .addr_i             (led_if.addr_i              ),
      .write_data_i       (led_if.write_data_i        ),
      .read_data_o        (led_if.read_data_o         ),
      .ready_o            (led_if.ready_o             ),
      .led_o              (led_o                      )

    );




property check_led_o;
  @(posedge clk_i) (!leds.led_mode && !resetn_i) |=> (led_o == leds.led_val)
endproperty


assert property (check_led_o) else begin
  $error("led_o != led_val. Expected: %0h, Got: %0h, at Time: %0t.",
         leds.led_val, led_o, $realtime); err_count++; 
end


property check_read_data_o_read_led_val;
  @(posedge clk_i)
    (led_if.req_i && !led_if.write_enable_i && (led_if.addr_i == ADDR_LED_VAL)) |=> (led_if.read_data_o == {16'h0, leds.led_val});
endproperty

assert property (check_read_data_o_read_led_val) else begin
      $error("read_data_o did not match the led_val_reg after read request. Expected: %0h, Got: %0h, at Time: %0t.", 
            {16'h0, $sampled(leds.led_val)}, $sampled(led_if.read_data_o), $realtime); err_count++;
end


property check_led_o_write_led_val;
  @(posedge clk_i)  disable iff (resetn_i)
  (led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_VAL) && (led_if.write_data_i <= MAX_LED_VAL)) |=> (led_o == led_if.write_data_i[15:0]);
endproperty

assert property (check_led_o_write_led_val) else begin
  $error("led_o did not update correctly after write to LED_VAL. Expected: %0h, Got: %0h, at Time: %0t.", 
          led_if.write_data_i[15:0], led_o, $realtime); err_count++; 
end


property check_led_o_read;
  @(posedge clk_i) (led_if.req_i && !led_if.write_enable_i && ((led_if.addr_i == ADDR_LED_VAL) || (led_if.addr_i == ADDR_LED_MODE) || (led_if.addr_i == ADDR_LED_RST ))) |=> ($stable(led_o));
endproperty

assert property (check_led_o_read) else begin
  $error(" led_o changed unexpectedly after read operation . Expected: %0h, Got: %0h, at Time: %0t.", 
           $past(led_o, 1), led_o, $realtime); err_count++; 
end


property check_read_data_o_write;
  @(posedge clk_i) (led_if.req_i && led_if.write_enable_i && ((led_if.addr_i == ADDR_LED_VAL ) || (led_if.addr_i == ADDR_LED_MODE ) || (led_if.addr_i == ADDR_LED_RST ))) |=> ($stable(led_if.read_data_o));
endproperty

assert property (check_read_data_o_write) else begin
  $error(" read_data_o changed unexpectedly after write operation to LED control registers. Expected: %0h, Got: %0h, at Time: %0t.", 
           $past(led_if.read_data_o, 1), led_if.read_data_o, $realtime); err_count++; 
end


property check_led_o_write_led_mode;
  @(posedge clk_i) (led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_MODE)) |=> ($stable(led_o));
endproperty

assert property (check_led_o_write_led_mode) else begin
  $error(" led_o changed unexpectedly after writing to ADDR_LED_MODE. Expected: %0h, Got: %0h, at Time: %0t.", 
           $past(led_o, 1), led_o, $realtime); err_count++; 
end

property check_led_mode_write_led_mode;
  @(posedge clk_i) disable iff (resetn_i)
   (led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_MODE)) |=> (leds.led_mode == led_if.write_data_i[0]);
endproperty

assert property (check_led_mode_write_led_mode) else begin
  $error("led_mode register did not update correctly after writing to ADDR_LED_MODE. Expected: %0h, Got: %0h, at Time: %0t.", 
          led_if.write_data_i[0], leds.led_mode, $realtime); err_count++; 
end


property check_read_data_o_read_led_mode;
  @(posedge clk_i) (led_if.req_i && !led_if.write_enable_i && (led_if.addr_i == ADDR_LED_MODE)) |=> (led_if.read_data_o == {31'h0, leds.led_mode});
endproperty

assert property (check_read_data_o_read_led_mode) else begin
      $error(" read_data_o did not match the led_mode_reg after read request. Expected: %0h, Got: %0h, at Time: %0t.", 
               {31'h0, leds.led_mode}, led_if.read_data_o, $realtime); err_count++; 
end


property check_led_o_write_rst;
  @(posedge clk_i) ((led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_RST)) || resetn_i) |=> (led_o == 0);
endproperty

assert property (check_led_o_write_rst) else begin
  $error(" led_o did not reset to 0 after write to ADDR_LED_RST or during reset. Expected: 0, Got: %0h, at Time: %0t.", 
           led_o, $realtime); err_count++; 
end

property check_rst_read;
  @(posedge clk_i) ((led_if.req_i && !led_if.write_enable_i && (led_if.addr_i == ADDR_LED_RST)) && !resetn_i) |=> ($stable(led_if.read_data_o));
endproperty

assert property (check_rst_read) else begin
  $error(" read_data_o changed unexpectedly after read request to ADDR_LED_RST or rst_i. Expected: %0h, Got: %0h, at Time: %0t.", 
           $past(led_if.read_data_o, 1), led_if.read_data_o, $realtime); err_count++; 
end


property check_regs_write_rst;
  @(posedge clk_i) ((led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_RST)) || resetn_i) |=> (leds.led_mode == 0 && leds.led_val == 0);
endproperty

assert property (check_regs_write_rst) else begin
  $error(" led_mode and led_val did not reset to 0 after write to ADDR_LED_RST or rst_i at Time: %0t.", 
           $realtime); err_count++; 
end


property check_led_o_write_led_val_max;
  @(posedge clk_i) (led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_VAL) && (led_if.write_data_i > MAX_LED_VAL)) |=> ($stable(led_o));
endproperty

assert property (check_led_o_write_led_val_max) else begin
  $error(" led_o changed unexpectedly after attempt to write above MAX_LED_VAL. Expected: %0h, Got: %0h, at Time: %0t.", 
           $past(led_o, 1), led_o, $realtime); err_count++; 
end


property check_read_data_o_without_access;
 @(posedge clk_i) disable iff (resetn_i)
  (!led_if.req_i ) |=> ($stable(led_if.read_data_o));
endproperty

assert property (check_read_data_o_without_access) else begin
  $error(" read_data_o changed without read access. Expected: %0h, Got: %0h, at Time: %0t.",
          $past(led_if.read_data_o , 1), led_if.read_data_o, $realtime); err_count++;
end


property check_led_o_without_access;
  @(posedge clk_i) disable iff (resetn_i)
  (!led_if.req_i ) |=> ($stable(led_o));
endproperty

assert property (check_led_o_without_access) else begin
  $error(" led_o changed without write access. Expected: %0h, Got: %0h, at Time: %0t.",
          $sampled($past(led_o , 1)), $sampled(led_o), $realtime);err_count++;
end

property check_read_data_o_restn;
  @(posedge clk_i) ((led_if.req_i && led_if.write_enable_i && (led_if.addr_i == ADDR_LED_RST)) || resetn_i) |=> (led_if.read_data_o == 0);
endproperty

assert property (check_read_data_o_restn) else begin
  $error(" read_data_o is not reset. Expected: %0h, Got: %0h, at Time: %0t.",
          0, led_if.read_data_o, $realtime); err_count++;
end


  task base_test();
  
    leds_write_val_test();
    leds_read_val_test();
    
    leds_write_mode_test();

    leds_read_rst_test();

    leds_read_mode_test();
    
    leds_write_rst_test();
  endtask

  task leds_write_val_test();
    @(posedge clk_i);
  
    led_if.write_request(ADDR_LED_VAL, $urandom_range(32'hffff, 0));
  endtask


  task leds_write_val_max_test();
  
    @(posedge clk_i);
  
    led_if.write_request(ADDR_LED_VAL, MAX_LED_VAL);
  
  endtask


  task leds_read_val_test();
  
    @(posedge clk_i);
    
    led_if.read_request(ADDR_LED_VAL);
        
  endtask


  task leds_write_rst_test(); 

    @(posedge clk_i);
  
    led_if.write_request(ADDR_LED_RST, 1); 
  
    led_if.write_request(ADDR_LED_RST, 0);
  
  endtask


  task leds_read_rst_test();
  
    @(posedge clk_i);
   
    led_if.read_request(ADDR_LED_RST);
    
  endtask

  task leds_ignore_value_test();
  
    @(posedge clk_i);
  
    led_if.write_request(ADDR_LED_VAL, 32'hfffff);  

  endtask


  task leds_write_mode_test();

    @(posedge clk_i);
   
    led_if.write_request(ADDR_LED_MODE, 1);  
  
    led_if.write_request(ADDR_LED_MODE, 0);


  endtask

  task leds_read_mode_test();

    @(posedge clk_i);
     
    led_if.read_request(ADDR_LED_MODE);

  endtask

  task leds_cntr_test();
  
    @(posedge clk_i);

    last_led_o = led_o;
    last_read_data_o = led_if.read_data_o;
  
    led_if.write_request(ADDR_LED_MODE, 1); 
    
    assert (led_if.read_data_o == last_read_data_o) else begin
      $error ("read_data_o should remain unchanged after writing Expected: %0h, Got: %0h, at Time: %0t.", 
               last_read_data_o, led_if.read_data_o, $realtime); err_count++; 
    end

    assert (led_o == leds.led_val) else begin
      $error ("led_o does not match the led_val Expected: %0h, Got: %0h, at Time: %0t.", 
               leds.led_val, led_o, $realtime); err_count++; 
    end

    #1ms;

    assert (led_if.read_data_o == last_read_data_o) else begin
      $error(" read_data_o  should remain stable 1 ms after the write operation. Expected: %0h, Got: %0h, at Time: %0t.", 
               last_read_data_o, led_if.read_data_o, $realtime); err_count++;  
    end

    assert (led_o == 0) else begin
      $error ("led_o did not turn off 1 ms after the write operation Expected: 0, Got: %0h, at Time: %0t.", 
               led_o, $realtime); err_count++; 
    end

    #1ms;

    assert (led_o == leds.led_val) else begin
      $error ("led_o did not return to its original value 2 ms after the write operation. Expected: %0h, Got: %0h, at Time: %0t.", 
               leds.led_val, led_o, $realtime); err_count++; 
    end
  endtask


  task leds_access_without_change(access_type_t access_type);
  
    @(posedge clk_i);
    for (int i = 0; i < 3; i++) begin
      if (access_type == WRITE) begin
        led_if.write_without_access(address_list[i], $urandom_range(32'hFFFF, 0));
      end else begin
        led_if.read_without_access(address_list[i]);
      end
    end
  endtask


  task leds_reset_test();

    @(posedge clk_i);

    ->leds_reset_begin;
    
    repeat(2)
      @(posedge clk_i);


    led_if.read_request(ADDR_LED_VAL);

      @(posedge clk_i);

    led_if.write_request(ADDR_LED_VAL, $urandom_range(32'hffff, 0)); 
    
      @(posedge clk_i);

    led_if.write_request(ADDR_LED_MODE, 1); 

    @(posedge clk_i);

    -> leds_reset_end;

  endtask


  initial begin

    err_count = 0;

    $timeformat(-9, 3, "ns", 8);

    repeat(2)
      @(posedge clk_i);
  
    base_test();

    leds_write_val_max_test();  
 
    leds_ignore_value_test();
 
    leds_access_without_change(READ);
    leds_access_without_change(WRITE);
 

    leds_write_val_test();
    leds_read_val_test();
    leds_reset_test();
   
    leds_write_val_test();
    leds_read_val_test();
    leds_cntr_test();

   test_finished = 1;
  end



  initial begin
    clk_i = 0;
    forever #5 clk_i = ~clk_i;
  end

  initial begin

    resetn_i = 1;

    repeat(2)
      @(posedge clk_i);
  
    resetn_i = 0;

    @leds_reset_begin;

    resetn_i = 1;

    @leds_reset_end;

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