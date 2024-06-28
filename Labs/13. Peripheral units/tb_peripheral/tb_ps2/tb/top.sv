`include "../interface.sv"
module tb_ps2();

  parameter [31:0] ADDR_SCAN_CODE  = 32'b0;
  parameter [31:0] ADDR_IS_UNREAD = 32'h04;
  parameter [31:0] ADDR_RS2_RST  = 32'h024;


  logic        clk_i;  
  logic        resetn_i;

  logic [31:0] addr;
  logic [31:0] last_read_data_o; 
  logic [31:0] data;

  peripheral_if ps2_if(clk_i);

  static logic [31:0] address_list_with_r_access [2] = {ADDR_SCAN_CODE, ADDR_IS_UNREAD};
  static logic [31:0] address_list[3] = {ADDR_SCAN_CODE, ADDR_IS_UNREAD, ADDR_RS2_RST};

  typedef enum {READ, WRITE} access_type_t;

  event ps2_reset;
  // event ps2_reset_end;
  // event ps2_reset_begin;


  ps2_sb_ctrl ps2(
      .rst_i               (resetn_i                   ),
      .clk_i               (clk_i                      ),
      .req_i               (ps2_if.req_i               ),
      .write_enable_i      (ps2_if.write_enable_i      ),
      .addr_i              (ps2_if.addr_i              ),
      .write_data_i        (ps2_if.write_data_i        ),
      .read_data_o         (ps2_if.read_data_o         ),
      .ready_o             (ps2_if.ready_o             ),
      .interrupt_request_o (ps2_if.interrupt_request_o ),
      .interrupt_return_i  (ps2_if.interrupt_return_i  )


    );
    
  sequence read_request;
     (ps2_if.req_i && !ps2_if.write_enable_i);
  endsequence

  sequence write_request;
     (ps2_if.req_i && ps2_if.write_enable_i);
  endsequence

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // property stability_read_request_scan_code;
  //     @(posedge clk_i) read_request |=>  $stable(ps2.scan_code) 
  // endproperty


  // assert property (stability_read_request_scan_code) else begin
  //     $error("scan_code changed unexpectedly during read request Expected: %0h, Got: %0h, at Time: %0t.", 
  //             $past(ps2.scan_code, 1),  ps2.scan_code, $realtime);
  // end
//////////////////////////////////////////////////////////////////////////////////////////////////////////////


  property stability_write_request;
      @(posedge clk_i) write_request |=> ($stable(ps2_if.read_data_o))
  endproperty

  assert property (stability_write_request) else begin
    $error("read_data_o changed unexpectedly during write request Expected: %0h, Got: %0h, at Time: %0t.", 
            $past(ps2_if.read_data_o, 1),  ps2_if.read_data_o, $realtime);
  end


  property check_scan_code_is_unread;
    @(posedge clk_i) (ps2.keycode_valid_o == 1) |=> (ps2_if.interrupt_request_o == 1);
  endproperty

    assert property (check_scan_code_is_unread) else begin
      $error("The interrupt request must be active when keycode_valid Time: %0t.", $realtime);
    end
//////////////////////////////////////////////////////////////////////////////////////////////////////

//   property check_scan_code;
//     @(posedge clk_i) (ps2.keycode_valid_o == 1) |=> (ps2.scan_code == $past(ps2.keycodeout_o, 1));
//   endproperty

//   assert property (check_scan_code) else begin
//     $error("Scan_code does not match keycodeout_o after activating keycode_valid. Expected: %0h, Got: %0h, at Time: %0t.",
//                ps2.keycodeout_o, $past(ps2.scan_code, 1), $realtime);
// end

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  property check_read_data_o_scan_code;
    @(posedge clk_i) (ps2_if.req_i && !ps2_if.write_enable_i && (ps2_if.addr_i == ADDR_SCAN_CODE)) |=> (ps2_if.read_data_o == {24'h0, ps2.scan_code});
  endproperty

  assert property (check_read_data_o_scan_code) else begin
    $error("Read_data_o does not match the expected scan_code value after read request (read_data_o != scan_code). Expected: %0h, Got: %0h, at Time: %0t.",
            {24'h0, ps2.scan_code}, ps2_if.read_data_o, $realtime);
end

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//   property check_stability_write_scan_code;
//     @(posedge clk_i) (ps2_if.req_i && ps2_if.write_enable_i && (ps2_if.addr_i == ADDR_SCAN_CODE)) |=> ($stable(ps2.scan_code));
//   endproperty

//   assert property (check_stability_write_scan_code) else begin
//     $error("scan_code changed unexpectedly during write operation. Expected: %0h, Got: %0h, at Time: %0t.",
//             $past(ps2.scan_code, 1), ps2.scan_code, $realtime);
// end

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



  property check_scan_code_read_operation_and_keycode;
    @(posedge clk_i) (ps2_if.req_i && !ps2_if.write_enable_i && (ps2_if.addr_i == ADDR_SCAN_CODE) && ps2.keycode_valid_o) |=> (ps2_if.interrupt_request_o == 1);
  endproperty

  assert property (check_scan_code_read_operation_and_keycode) else begin
    $error("interrupt_request_o was not activated when keycode_valid_ o = 1 during scan_code read operation. Expected: 1, Got: %0h, at Time: %0t.",
             ps2_if.interrupt_request_o, $realtime);
  end


  property check_scan_code_read_operation;
    @(posedge clk_i) (ps2_if.req_i && !ps2_if.write_enable_i && (ps2_if.addr_i == ADDR_SCAN_CODE) && !ps2.keycode_valid_o) |=> (ps2_if.interrupt_request_o == 0);
  endproperty

  assert property (check_scan_code_read_operation) else begin
    $error("interrupt_request_o was sent incorrectly when during a SCAN_CODE read operation keycode_valid_o = 0. Expected: 0, Got: %0h, at Time: %0t.",
             ps2_if.interrupt_request_o, $realtime);
  end






  // property check_stability_write_scan_code_is_unread;
  //   @(posedge clk_i) (ps2_if.req_i && ps2_if.write_enable_i && (ps2_if.addr_i == ADDR_IS_UNREAD)) |=> ($stable(ps2.scan_code_is_unread));
  // endproperty

  // property check_scan_code_is_unread_interrupt_return_i;
  //   @(posedge clk_i) (ps2_if.interrupt_return_i && !ps2.keycode_valid_o) |-> (ps2_if.interrupt_request_o == 0);
  // endproperty

  // property check_scan_code_is_unread_interrupt_return_i_and_keycode;
  //   @(posedge clk_i) (ps2_if.interrupt_return_i && ps2.keycode_valid_o) |-> (ps2_if.interrupt_request_o == 1);
  // endproperty

  // property check_scan_code_is_unread_read_operation;
  //   @(posedge clk_i) (ps2_if.req_i && !ps2_if.write_enable_i && (ps2_if.addr_i == 32'h04) ) |-> (ps2_if.read_data_o == ps2.scan_code_is_unread);
  // endproperty

  // property check_rst_write_operation;
  //   @(posedge clk_i) (ps2_if.req_i && ps2_if.write_enable_i && (ps2_if.addr_i == 32'h024) ) |-> ((ps2.scan_code_is_unread == 0) &&  (ps2.scan_code == 0));
  // endproperty



  task ps2_read_scan_code_is_unread();
  
  repeat (3) begin 
  @(posedge clk_i);
  ps2.scan_code_is_unread <= $random;
    for (int i = 0; i < 2; i++ ) begin

      ps2.keycode_valid_o <= i;

      @(posedge clk_i);


      ps2_if.read_request(ADDR_IS_UNREAD);

    end
  end
  endtask



  task ps2_read_scan_code();
  repeat (3) begin
      
  @(posedge clk_i);
    for (int i = 0; i < 2; i++ ) begin

      ps2.keycodeout_o <= $random;
      ps2.keycode_valid_o <= i;

      @(posedge clk_i);


      ps2_if.read_request(ADDR_SCAN_CODE);

    end
  end
  endtask


  task ps2_write_scan_code();

  repeat (3) begin
      
  @(posedge clk_i);
    for (int i = 0; i < 2; i++ ) begin

      ps2.keycodeout_o <= $random;
      ps2.keycode_valid_o <= i;

      @(posedge clk_i);


      ps2_if.write_request(ADDR_SCAN_CODE, $urandom_range(32'hff, 0));

    end
  end
  endtask


  task ps2_write_scan_code_is_unread();
    @(posedge clk_i);
      
    ps2.scan_code_is_unread <= $random;
    for (int i = 0; i < 2; i++ ) begin

      ps2.keycode_valid_o <= i;

      @(posedge clk_i);


      ps2_if.write_request(ADDR_IS_UNREAD, $urandom_range(32'b1, 0));

    end
  endtask



  // task ps2_write_rst();  

  // @(posedge clk_i);

  // ps2_if.write_request(ADDR_RS2_RST, 1);

  // @(posedge clk_i);

 // ps2_if.write_request(ADDR_RS2_RST, 1);

  // endtask


  // task ps2_reset_test();
 
  //   ->ps2_reset_begin;
  
  //   repeat(2)
  //     @(posedge clk_i);
  
  //   ps2_if.read_request(32'h0);
 
  //   @(posedge clk_i);
  
  //   ps2_if.interrupt_return();
  
  //   @(posedge clk_i);

  //   ps2_if.write_request(32'b0, $urandom_range(16'hFFFF, 0));

  //   repeat(2)
  //     @(posedge clk_i);

  //   ->ps2_reset_end;

  //   ps2_if.interrupt_return();
  // endtask



  // task ps2_read_rst();

  // @(posedge clk_i);

  // for (int i = 0; i <= 1; i++ ) begin
  //   ps2.keycode_valid_o = i;
  //   ps2_if.write_request(ADDR_RS2_RST, 1);
  // end

  // endtask


  // task ps2_rst(); //взять с предыдущего тестбенча

  // endtask

  // task ps2_interrupt_return_i();

  //   @(posedge clk_i);

  // for (int i = 0; i <= 1; i++ ) begin
  //   ps2.keycode_valid_o = i;
  //   ps2_if.interrupt_return();
  // end
  // endtask

  
  // запрос на чтение scan_code + (keycode_valid_o == 0) = (read_data_o == scan_code) +  (scan_code_is_unread == 0)

  // запрос на чтение scan_code +  (keycode_valid_o == 1) = (scan_code_is_unread == 1)

  // interrupt_return_i  == 1  && (keycode_valid_o == 0)  =  (scan_code_is_unread == 0)

  // запрос на чтение scan_code_is_unread

  // запрос на запись rst, сброс регистров scan_code и scan_code_is_unread






  initial begin

    repeat(2)
      @(posedge clk_i); 
    ps2_read_scan_code_is_unread();
    ps2_read_scan_code();
    ps2_write_scan_code();
    ps2_write_scan_code_is_unread();

    repeat (3)
     @(posedge clk_i)

    $finish;
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

  end

endmodule