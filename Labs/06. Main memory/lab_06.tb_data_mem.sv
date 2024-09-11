/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_06_tb_data_mem;
  // Входы
  import memory_pkg::DATA_MEM_SIZE_WORDS;
  import memory_pkg::DATA_MEM_SIZE_BYTES;

  logic        clk_i;
  logic        mem_req_i;
  logic        write_enable_i;
  logic [3:0]  byte_enable_i;
  logic [31:0] addr_i, addr;
  logic [31:0] write_data_i;
  assign addr = addr_i[2+:$clog2(DATA_MEM_SIZE_WORDS)];

  logic [31:0] read_data_o;
  logic        ready_o;


  logic [31:0]  last_read_data;
  logic [31:0]  last_write_data;

  int err_cnt = 0;

  data_mem DUT (.*);

  task read_request(input logic [31:0] address, output logic [31:0] data);
    addr_i          <= address;
    mem_req_i       <= 1'b1;
    write_enable_i  <= 1'b0;
    @(posedge clk_i);
    data = read_data_o;
    mem_req_i       <= 1'b0;
  endtask

  task write_request( input logic [31:0] address, data, input [3:0] be);
    addr_i          <= address;
    mem_req_i       <= 1'b1;
    write_enable_i  <= 1'b1;
    byte_enable_i   <= be;
    write_data_i    <= data;
    @(posedge clk_i);
    mem_req_i       <= 1'b0;
  endtask

  task direct_read_test();
    logic [31:0] data;
    for(int i = 0; i < 128; i++) begin
      read_request(i, data);
    end
    if(DATA_MEM_SIZE_BYTES > 128) begin
      for(int i = 1; i <= 128; i++) begin
        read_request(DATA_MEM_SIZE_BYTES / 128 * i + i%4, data);
      end
    end
  endtask

  task direct_write_test();
    for(int i = 0; i < 128; i++) begin
      write_request(i, $urandom(), '1);
    end
    if(DATA_MEM_SIZE_BYTES > 128) begin
      for(int i = 1; i <= 128; i++) begin
        write_request(DATA_MEM_SIZE_BYTES / 128 * i + i%4, $urandom(), i%16);
      end
    end
  endtask

  task random_write_test();
    repeat(1000) begin
      write_request($urandom_range(0, DATA_MEM_SIZE_BYTES-1), $urandom(), $urandom_range(0, 15));
    end
    repeat(1000) begin
      write_request($urandom(), $urandom(), $urandom_range(0, 15));
    end
  endtask

  task random_read_test();
    logic [31:0] data;
    repeat(1000) begin
      read_request($urandom_range(0, DATA_MEM_SIZE_BYTES-1), data);
    end
    repeat(1000) begin
      read_request($urandom(), data);
    end
  endtask

  task incorrect_read_test();
    mem_req_i       <= '0;
    write_enable_i  <= '1;
    addr_i          <= '0;
    @(posedge clk_i);
    write_enable_i <= '0;
    @(posedge clk_i);
    mem_req_i <= '1;
    @(posedge clk_i);
  endtask

  task incorrect_write_test();
    mem_req_i       <= '0;
    write_enable_i  <= '0;
    byte_enable_i   <= '0;
    write_data_i    <= '1;
    addr_i          <= '0;
    @(posedge clk_i);
    mem_req_i       <= '1;
    @(posedge clk_i);
    write_enable_i  <= '1;
    @(posedge clk_i);
    byte_enable_i   <= 4'b0010;
    @(posedge clk_i);
  endtask

  task random_test();
    repeat(1000) begin
      mem_req_i       <= $urandom_range(1);
      write_enable_i  <= $urandom_range(1);
      byte_enable_i   <= $urandom_range(15);
      addr_i          <= $urandom();
      write_data_i    <= $urandom();
      @(posedge clk_i);
    end
  endtask

  initial begin
    $timeformat(-9, 3, "ns", 8);
    $display("Test has been started");

    DUT.ram[0] = '0;
    DUT.ram[DATA_MEM_SIZE_WORDS-1] = '0;
    DUT.ram[DATA_MEM_SIZE_WORDS] = '0;
    assert( DUT.ram[0] == 0) else begin
      $display("RAM has no element with index 0");
      $fatal;
    end
    assert( DUT.ram[DATA_MEM_SIZE_WORDS-1] == 0) else begin
      $display("RAM has no element with index %d", DATA_MEM_SIZE_WORDS-1);
      $fatal;
    end
    assert( DUT.ram[DATA_MEM_SIZE_WORDS] === 'x) else begin
      $display("RAM has element with index %d", DATA_MEM_SIZE_WORDS);
      $fatal;
    end
    assert( DUT.ram[0][0] == 0) else begin
      $display("RAM bit indexes started not from 0");
      $fatal;
    end
    assert( DUT.ram[0][31] == 0) else begin
      $display("RAM bit indexes ended not at 31");
      $fatal;
    end
    assert( DUT.ram[0][32] === 'x) else begin
      $display("RAM bit indexes ended not at 31");
      $fatal;
    end

    direct_write_test();
    direct_read_test();
    random_write_test();
    random_read_test();
    incorrect_read_test();
    incorrect_write_test();
    random_test();

    $display("\nTest has been finished\nNumber of errors: %d\n", err_cnt);
    $finish;
    #5;
    $display("You're trying to run simulation that has finished. Aborting simulation.");
    $fatal();
  end

  logic [31:0] ram_data;
  logic [31:0] addr_reg;
  always @(posedge clk_i) begin
    addr_reg <= addr;
  end
  assign ram_data = DUT.ram[addr_reg];


  initial begin
    clk_i = 0;
    forever #5 clk_i = ~clk_i;
  end

  ready_check: assert property (@(posedge clk_i) ready_o) else begin
    err_cnt++;
    $display("Error at %t. Value of ready is not equal 1.", $time);
  end

  correct_read_check: assert property (
    @(posedge clk_i)
    mem_req_i & !write_enable_i |=> read_data_o === ram_data
  ) else begin
    err_cnt++;
    $display("Error at %t. Incorrect read_data_o: %08h instead of %08h", $time(), $sampled(read_data_o), $sampled(ram_data));
  end

  logic [31:0] write_data;
  always @(posedge clk_i) begin
    write_data <= write_data_i;
  end

  correct_write_check_0: assert property (
    @(posedge clk_i)
    mem_req_i & write_enable_i & byte_enable_i[0]|=> $past(write_data_i[7:0]) === ram_data[7:0]
  ) else begin
    err_cnt++;
    $display("Error at %t. Incorrect value of ram[%01d][7:0]: %02h instead of %02h", $time(), $sampled(addr_reg), $sampled(ram_data[7:0]), $sampled(write_data_i[7:0]));
  end
  correct_write_check_1: assert property (
    @(posedge clk_i)
    mem_req_i & write_enable_i & byte_enable_i[1]|=> $past(write_data_i[15:8]) == ram_data[15:8]
  ) else begin
    err_cnt++;
    $display("Error at %t. Incorrect value of ram[%01d][15:8]: %02h instead of %02h", $time(), $sampled(addr_reg), $sampled(ram_data[15:8]), $sampled(write_data_i[15:8]));
  end
  correct_write_check_2: assert property (
    @(posedge clk_i)
    mem_req_i & write_enable_i & byte_enable_i[2]|=> $past(write_data_i[23:16]) == ram_data[23:16]
  ) else begin
    err_cnt++;
    $display("Error at %t. Incorrect value of ram[%d][23:16]: %02h instead of %02h", $time(), $sampled(addr_reg), $sampled(ram_data[23:16]), $sampled(write_data_i[23:16]));
  end
  correct_write_check_3: assert property (
    @(posedge clk_i)
    mem_req_i & write_enable_i & byte_enable_i[3]|=> $past(write_data_i[31:24]) == ram_data[31:24]
  ) else begin
    err_cnt++;
    $display("Error at %t. Incorrect value of ram[%d][31:24]: %02h instead of %02h", $time(), $sampled(addr), $sampled(ram_data[31:24]), $sampled(write_data_i[31:24]));
  end

  incorrect_read_check: assert property (
    @(posedge clk_i)
    !mem_req_i | write_enable_i |=> $stable(read_data_o)
  ) else begin
    err_cnt++;
    $display("Error at %t. read_data_o is unstable without read request", $time());
  end

  incorrect_write_check_0: assert property (
    @(posedge clk_i)
    (!mem_req_i | !write_enable_i | !byte_enable_i[0]) & $stable(addr) |=> $stable(ram_data[7:0])
  ) else begin
    err_cnt++;
    $display("Error at %t. ram[%d][7:0] is unstable without write request", $time(), $sampled(addr_reg));
  end
  icorrect_write_check_1: assert property (
    @(posedge clk_i)
    (!mem_req_i | !write_enable_i | !byte_enable_i[1]) & $stable(addr) |=> $stable(ram_data[15:8])
  ) else begin
    err_cnt++;
    $display("Error at %t. ram[%d][15:8] is unstable without write request", $time(), $sampled(addr_reg));
  end
  incorrect_write_check_2: assert property (
    @(posedge clk_i)
    (!mem_req_i | !write_enable_i | !byte_enable_i[2]) & $stable(addr) |=> $stable(ram_data[23:16])
  ) else begin
    err_cnt++;
    $display("Error at %t. ram[%d][23:16] is unstable without write request", $time(), $sampled(addr_reg));
  end

  incorrect_write_check_3: assert property (
    @(posedge clk_i)
    (!mem_req_i | !write_enable_i | !byte_enable_i[3]) & $stable(addr) |=> $stable(ram_data[31:24])
  ) else begin
    err_cnt++;
    $display("Error at %t. ram[%d][31:24] is unstable without write request", $time(), $sampled(addr_reg));
  end

  always @(posedge clk_i) begin
    if (err_cnt >= 10) begin
      $display("\nTest has been stopped after 10 errors"); $stop();
    end
  end

endmodule
