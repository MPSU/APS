`timescale 1ns/1ps
module top;
  // Входы
  import riscv_pkg::DATA_MEM_SIZE_WORDS;

  logic        clk_i;
  logic        mem_req_i;
  logic        write_enable_i;
  logic [3:0]  byte_enable_i;
  logic [31:0] addr_i;
  logic [31:0] write_data_i;

  // Выходы
  logic [31:0] read_data_o;
  logic        ready_o;


  logic [31:0]  last_read_data;
  logic [31:0]  last_write_data;

  int err_count = 0;

  static bit  simulation_finished;

   ext_mem DUT (

   .clk_i             (  clk_i           ),

   .write_enable_i    (  write_enable_i  ),
   .byte_enable_i     (  byte_enable_i   ),
   .mem_req_i         (  mem_req_i       ),

   .addr_i            (  addr_i          ),
   .write_data_i      (  write_data_i    ),


   .read_data_o       (  read_data_o    ),
   .ready_o           (  ready_o        )

 );


  assert property (@(posedge clk_i) always (ready_o === 1'b1))
    else $error("Error: Incorrect ready_o- Expected: %0d, Got at time: %0d", 1, ready_o, $realtime);


  task ram_size_test();
  
    $display("START ram_size_test");

    assert( DUT.ram.size() == DATA_MEM_SIZE_WORDS) else begin 
      $error(
        "Error: Incorrect RAM size (depth)  Expected: %0d, Got: %0d",
                                  DATA_MEM_SIZE_WORDS, DUT.ram.size()
      ); $fatal; end

    assert( $bits(DUT.ram[0]) == 32              ) else begin 
      $error(
        "Error: Incorrect RAM size (length) Expected: %0d, Got: %0d",
                                               32, $bits(DUT.ram[0]) 
      ); $fatal; end
   
    $display("END   ram_size_test");
  endtask



  task initialization_zero_ram();
  
    $display("START initialization_zero_ram");
  
    for (int i = 0; i < DATA_MEM_SIZE_WORDS; i++) begin
      DUT.ram[i] = 32'h0; 
    end
  
    $display("END   initialization_zero_ram");
  endtask


  task check_boundary_address();
  
    $display("START check_boundary_address");
  
    addr_i  =  0;
   
    assert(DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]]    == 32'h0) else begin      
      $error(
        "Error: Wrong boundaries, non-deterministic data in zero address (depth) Expected: %0d, Got: %0d", 0,
                                                             DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] 
      ); $fatal; end
    
    assert(DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]][0] == 0) else begin 
      $error(
        "Error: Wrong boundaries, non-deterministic data in zero address (length) Expected: %0d, Got: %0d", 
                                                    0, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]][0] 
      ); $fatal; end
  
    $display("END   check_boundary_address");
  
  endtask

  task base_test();

    $display("START base_test");

    write_mem_test();

    read_after_write_test();

    write_after_read_test();

    $display("END   base_test");
  endtask

task write_mem_test();
 
 // write  
  @(posedge clk_i);

  mem_req_i      <=  1;
  write_enable_i <=  1;
  byte_enable_i  <= '1;

  addr_i         <= $urandom_range(32'hffff_ffff, 0);
  write_data_i   <= $urandom_range(32'hffff_ffff, 0);

repeat(2)
  @(posedge clk_i);
   
  assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] == write_data_i) else begin
    $error(
      "Error: incorrect data in ram when writing Expected: %0h, Got: %0h. Time %0t", 
          write_data_i, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
    ); 
    err_count = err_count + 1; 
  end

 // проверяем что помимо addr_i ничего не изменилось в ram  
  for (int i = 0; i < DATA_MEM_SIZE_WORDS; i++) begin
      if (i != addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]) begin
          assert(DUT.ram[i] == 32'h0) else begin
            $error(
              "Error: wrong address, a write is Expected at address: %0h, Got: %0h. Time: %0t", 
                                        addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2], i,  $realtime
            ); 
            err_count = err_count + 1;
          end
      end
  end

endtask

task read_after_write_test();

 // read after write
  write_enable_i <= 0;
  write_data_i <=  $urandom_range(32'hffff_ffff, 0);

  last_write_data <= DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]];

  repeat(2)
    @(posedge clk_i);
  // проверяем, что записи не было
  assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] == last_write_data) else begin 
    $error(
      "Error: incorrect data in ram was written while reading Expected: %0h, Got: %0h. Time: %0t", 
                    last_write_data, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
    );
    err_count = err_count + 1;
  end

    for (int i = 0; i < DATA_MEM_SIZE_WORDS; i++) begin
      if (i != addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]) begin
          assert(DUT.ram[i] == 32'h0) else begin
            $error(
              "Error: incorrect data in ram was written while reading Expected: %0h, Got: %0h. Time: %0t", 
                                      32'h0, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
            ); 
            err_count = err_count + 1;
          end
      end
  end

 // проверяем корректность чтения
  assert( read_data_o == last_write_data) else  begin
    $error("Reading Error: read_data_o  Expected: %0h, Got: %0h. Time: %0t", last_write_data, read_data_o, $realtime); 
    err_count = err_count + 1; 
  end

endtask

task write_after_read_test();

  @(posedge clk_i);
  // write after read 
  write_enable_i <= 1;
  write_data_i   <=  $urandom_range(32'hffff_ffff, 0);

  last_read_data <= read_data_o;

  repeat(2)
    @(posedge clk_i);

  //проверяем, что read_data_o не изменяется при записи
  assert( read_data_o == last_read_data) else begin
    $error("Error write: read_data_o Expected: %0h, Got: %0h. Time: %0t ", last_read_data, read_data_o, $realtime); 
    err_count = err_count + 1; 
  end 

endtask


task read_without_mem_access();

  // write
  $display("START read_without_mem_access");

  @(posedge clk_i);

  last_read_data <= read_data_o;

  mem_req_i      <=  1;
  write_enable_i <=  1;
  byte_enable_i  <= '1;

  addr_i         <= $urandom_range(32'hffff_ffff, 0);

  std::randomize (write_data_i) with {write_data_i != last_read_data ; };

  repeat(2)
    @(posedge clk_i);

  // read after write
  mem_req_i      <= 0;
  write_enable_i <= 0;

  repeat(2)
    @(posedge clk_i);

  assert( read_data_o == last_read_data) else begin
    $error("Error: read without access Expected: %0h, Got: %0h. Time: %0t", last_read_data, read_data_o, $realtime); 
    err_count = err_count + 1;
  end

  $display("END   read_without_mem_access");

endtask



task write_without_mem_access();

  $display("START write_without_mem_access");

  @(posedge clk_i);
  mem_req_i       <=  0;
  write_enable_i  <=  1;
  byte_enable_i   <= '1;

  addr_i          <= $urandom_range(32'hffff_ffff, 0);

  std::randomize (write_data_i) with {write_data_i != last_write_data ; };
    
  @(posedge clk_i);

  last_write_data = DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]];

  @(posedge clk_i);

  assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] == last_write_data) else  begin  
    $error(
      "Error: write without access Expected: %0h, Got: %0h. Time: %0t", 
        last_write_data, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
    ); 
    err_count = err_count + 1;
  end

  $display("END   write_without_mem_access");
endtask


task write_bytes();

  logic [31:0] initial_ram [DATA_MEM_SIZE_WORDS];

  $display("START write_byte");

  for (int i = 1; i < (1 << $bits(byte_enable_i)); i ++) begin 

    @(posedge clk_i);

    mem_req_i       <=  1;
    write_enable_i  <=  1;
    byte_enable_i   <=  i;

    write_data_i    <= $urandom_range(32'hffff_ffff, 0);

    addr_i          <= $urandom_range(32'hffff_ffff, 0);


    last_read_data  <= read_data_o;

    // save ram
    // for (int j = 0; j < DATA_MEM_SIZE_WORDS; j++) begin
    //   initial_ram[j] = DUT.ram[j];
    // end

    repeat(2)
      @(posedge clk_i);

    // проверяем что при записи read_data_o сохраняет свое значение   
    // assert (read_data_o == last_read_data ) else begin
    //     $error("Error write: read_data_o Expected: %0h, Got: %0h. Time: %0t ", last_read_data, read_data_o, $realtime); 
    //     err_count = err_count + 1; 
    // end 


    if (byte_enable_i[0])
      assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [7:0] == write_data_i[7:0]) else begin
        $error(
          "Error writing zero byte to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.", 
            addr_i, write_data_i[7:0], DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [7:0], $realtime
        ); 
        err_count = err_count + 1; 
      end

    if (byte_enable_i[1])
      assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [15:8] == write_data_i[15:8]) else begin
        $error(
          "Error writing first byte to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.", 
             addr_i, write_data_i[15:8], DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [15:8], $realtime
        ); 
        err_count = err_count + 1;
      end

    if (byte_enable_i[2])
      assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [23:16] == write_data_i[23:16]) else begin
        $error(
          "Error writing second byte to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.",
            addr_i, write_data_i[23:16], DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [23:16], $realtime
        ); 
        err_count = err_count + 1;
      end

    if (byte_enable_i[3])
      assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [31:24] == write_data_i[31:24]) else begin
        $error(
          "Error writing third byte to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.", 
            addr_i, write_data_i[31:24], DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [31:24], $realtime
        ); 
        err_count = err_count + 1; 
      end


  // проверяем что помимо addr_i ничего не изменилось в ram
    // for (int k = 0; k < DATA_MEM_SIZE_WORDS; k++) begin
    //   if (k != addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]) begin
    //       assert(DUT.ram[k] == initial_ram[k]) else 
    //         $error(
    //           "Error write, wrong address 
    //                   Expected: %0h, Got: %0h. Time: %0t.", addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2], i, $realtime
    //         );
    //   end
    // end
  end
  $display("END   write_byte");
endtask


  task write_null_byte();
    logic [31:0] data;
  
    $display("START write_null_byte");

    @(posedge clk_i);

    mem_req_i       <=  1;
    write_enable_i  <=  1;
    byte_enable_i   <=  1;

    write_data_i    <= 32'hffff_ffff;

    addr_i          <= $urandom_range(32'hffff_ffff, 0);

    @(posedge clk_i);

    data            <= DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]];

    @(posedge clk_i);

    assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [31:8] == data[31:8]) else begin
      $error(
        "Error writing zero byte to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.",
          addr_i, {data[31:8], write_data_i[7:0]}, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
      ); 
      err_count = err_count + 1; 
    end  

    $display("END   write_null_byte");
  endtask

  task write_first_byte();

    logic [31:0] data;

    $display("START write_first_byte"); 

    @(posedge clk_i);

    mem_req_i       <=  1;
    write_enable_i  <=  1;
    byte_enable_i   <=  2;

    write_data_i    <= 32'hffff_ffff;

    addr_i          <= $urandom_range(32'hffff_ffff, 0);

    @(posedge clk_i);

    data            <= DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]];

    @(posedge clk_i);

    assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [31:16] == data[31:16] && DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [7:0] == data[7:0]) else begin
      $error(
        "Error writing first byte to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.", 
          addr_i, {data[31:16], write_data_i[15:8], data[7:0]}, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
      ); 
      err_count = err_count + 1; 
    end  

    $display("END   write_first_byte"); 
  endtask


  task write_second_byte();
  
    logic [31:0] data;

    $display("START write_second_byte"); 

    @(posedge clk_i);

    mem_req_i       <=  1;
    write_enable_i  <=  1;
    byte_enable_i   <=  4;

    write_data_i    <= 32'hffff_ffff;

    addr_i          <= $urandom_range(32'hffff_ffff, 0);

    @(posedge clk_i);

    data            <= DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]];

    @(posedge clk_i);
  
    assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [31:24] == data[31:24] && DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [15:0] == data[15:0]) else begin
      $error(
        "Error writing second to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.", 
          addr_i, {data[31:24], write_data_i[23:16], data[15:0]}, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
      ); 
      err_count = err_count + 1; 
    end  
    $display("END   write_second_byte"); 
  endtask

  task write_third_byte();
  
    logic [31:0] data;

    $display("START write_third_byte"); 

    @(posedge clk_i);

    mem_req_i       <=  1;
    write_enable_i  <=  1;
    byte_enable_i   <=  8;

    write_data_i    <= 32'hffff_ffff;

    addr_i          <= $urandom_range(32'hffff_ffff, 0);

    @(posedge clk_i);

    data            <= DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]];

    @(posedge clk_i);

    assert(  DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]] [23:0] == data[23:0] ) else begin
      $error(
        "Error writing third to addr_i: %0h Expected: %0h, Got: %0h. Time: %0t.", 
           addr_i, {write_data_i[31:24], data[23:0]}, DUT.ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:2]], $realtime
      ); 
      err_count = err_count + 1; 
    end  
$display("END   write_third_byte"); 
  endtask


always @(posedge clk_i) begin 
  if(simulation_finished) begin
    $display("Simulation finished!"); 
    $finish;
  end
end

initial begin

  $timeformat(-9, 3, "ns", 8);

  ram_size_test();

  $display("--------------------------------------");   
  
  initialization_zero_ram();

  $display("--------------------------------------");

  check_boundary_address();
  
  $display("--------------------------------------");

  base_test();

  $display("--------------------------------------");
  
  read_without_mem_access();
  
  $display("--------------------------------------");
  
  write_without_mem_access();

  $display("--------------------------------------");

  write_null_byte();

  $display("--------------------------------------");

  write_first_byte();
    
  $display("--------------------------------------");

  write_second_byte();

  $display("--------------------------------------");

  write_third_byte();

  $display("--------------------------------------");

  write_bytes();

  $display("--------------------------------------");  
  
  $display("All tests finished, number of errors = %d", err_count);
  
  $finish;
    simulation_finished = 1;
end


initial begin
  clk_i = 0;
  forever #5 clk_i = ~clk_i;
end

endmodule
