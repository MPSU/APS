interface peripheral_if(input logic clk_i);
    logic req_i;
    logic write_enable_i;
    logic [31:0] addr_i;
    logic [31:0] write_data_i;
    logic [31:0] read_data_o;

    logic        interrupt_request_o;
    logic        interrupt_return_i;

    // logic        kclk_i;
    // logic        kdata_i;

    logic        ready_o;



  // assert property (@(posedge clk_i) always (ready_o === 1'b1))
  //   else $error("Error: Incorrect ready_o- Expected: %0d, Got at time: %0d", 1, ready_o);


    task automatic read_request( input logic [31:0] addr);

      req_i <= 1'b1;
      write_enable_i <= 1'b0;
      addr_i <= addr;
  
      @(posedge clk_i);
  
      req_i <= 1'b0;
  
      @(posedge clk_i);
   endtask


  task  automatic write_request(input logic [31:0] addr, input logic [31:0] write_data);

    req_i <= 1'b1;
    write_enable_i <= 1'b1;
    addr_i <= addr;
    write_data_i <= write_data;

    @(posedge clk_i);

    req_i <= 1'b0;
    // write_enable_i <= 1'b0;

    @(posedge clk_i);
  endtask

  task automatic read_without_access(input logic [31:0] addr);
    req_i <= 0;
    addr_i <= addr;
    write_enable_i <= 0;

    repeat(2)
      @(posedge clk_i);
  endtask


  task automatic write_without_access(input logic [31:0] addr, input logic [31:0] write_data);
  
    req_i <= 0;
    addr_i <= addr;
    write_enable_i <= 1;

    write_data_i <= write_data;


    repeat(2)
      @(posedge clk_i);
  endtask

    task interrupt_return();
      interrupt_return_i <= 1;
      @(posedge clk_i);
      interrupt_return_i <= 0;
      @(posedge clk_i);
  endtask
endinterface
