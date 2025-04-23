/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

module lab_05_tb_decoder();

  import decoder_pkg::*;
  typedef class riscv_instr;
  riscv_instr instr = new();

  logic clk;
  logic [31:0]  fetched_instr_i = '0;

  int err_count;

  //list of all valid opcodes
  logic [4:0] opcode_array[11] =  {
    LOAD_OPCODE,
    MISC_MEM_OPCODE,
    OP_IMM_OPCODE,
    AUIPC_OPCODE,
    STORE_OPCODE,
    OP_OPCODE,
    LUI_OPCODE,
    BRANCH_OPCODE,
    JALR_OPCODE,
    JAL_OPCODE,
    SYSTEM_OPCODE
    };

  /*
    Since randomize with overconstraining slows down simulation, it has been
    decided to make a list of all codes instead of looping over every possible
    combination func3 and func7.
  */
  logic [14:0] valid_codes[44] = {
    {LOAD_OPCODE    , 3'h0, 7'h00},
    {LOAD_OPCODE    , 3'h1, 7'h00},
    {LOAD_OPCODE    , 3'h2, 7'h00},
    {LOAD_OPCODE    , 3'h4, 7'h00},
    {LOAD_OPCODE    , 3'h5, 7'h00},
    {MISC_MEM_OPCODE, 3'h0, 7'h00},
    {OP_IMM_OPCODE  , 3'h0, 7'h00},
    {OP_IMM_OPCODE  , 3'h1, 7'h00},
    {OP_IMM_OPCODE  , 3'h2, 7'h00},
    {OP_IMM_OPCODE  , 3'h3, 7'h00},
    {OP_IMM_OPCODE  , 3'h4, 7'h00},
    {OP_IMM_OPCODE  , 3'h5, 7'h00},
    {OP_IMM_OPCODE  , 3'h5, 7'h20},
    {OP_IMM_OPCODE  , 3'h6, 7'h00},
    {OP_IMM_OPCODE  , 3'h7, 7'h00},
    {AUIPC_OPCODE   , 3'h0, 7'h00},
    {STORE_OPCODE   , 3'h0, 7'h00},
    {STORE_OPCODE   , 3'h1, 7'h00},
    {STORE_OPCODE   , 3'h2, 7'h00},
    {OP_OPCODE      , 3'h0, 7'h00},
    {OP_OPCODE      , 3'h0, 7'h20},
    {OP_OPCODE      , 3'h1, 7'h00},
    {OP_OPCODE      , 3'h2, 7'h00},
    {OP_OPCODE      , 3'h3, 7'h00},
    {OP_OPCODE      , 3'h4, 7'h00},
    {OP_OPCODE      , 3'h5, 7'h00},
    {OP_OPCODE      , 3'h5, 7'h20},
    {OP_OPCODE      , 3'h6, 7'h00},
    {OP_OPCODE      , 3'h7, 7'h00},
    {LUI_OPCODE     , 3'h0, 7'h00},
    {BRANCH_OPCODE  , 3'h0, 7'h00},
    {BRANCH_OPCODE  , 3'h1, 7'h00},
    {BRANCH_OPCODE  , 3'h4, 7'h00},
    {BRANCH_OPCODE  , 3'h5, 7'h00},
    {BRANCH_OPCODE  , 3'h6, 7'h00},
    {BRANCH_OPCODE  , 3'h7, 7'h00},
    {JALR_OPCODE    , 3'h0, 7'h00},
    {JAL_OPCODE     , 3'h0, 7'h00},
    {SYSTEM_OPCODE  , 3'h1, 7'h00},
    {SYSTEM_OPCODE  , 3'h2, 7'h00},
    {SYSTEM_OPCODE  , 3'h3, 7'h00},
    {SYSTEM_OPCODE  , 3'h5, 7'h00},
    {SYSTEM_OPCODE  , 3'h6, 7'h00},
    {SYSTEM_OPCODE  , 3'h7, 7'h00}
  };

  logic [14:0] invalid_codes[38] = {
    {LOAD_OPCODE    , 3'h3, 7'h00},
    {LOAD_OPCODE    , 3'h6, 7'h00},
    {LOAD_OPCODE    , 3'h7, 7'h00},
    {MISC_MEM_OPCODE, 3'h1, 7'h00},
    {MISC_MEM_OPCODE, 3'h2, 7'h00},
    {MISC_MEM_OPCODE, 3'h3, 7'h00},
    {MISC_MEM_OPCODE, 3'h4, 7'h00},
    {MISC_MEM_OPCODE, 3'h5, 7'h00},
    {MISC_MEM_OPCODE, 3'h6, 7'h00},
    {MISC_MEM_OPCODE, 3'h7, 7'h00},
    {OP_IMM_OPCODE  , 3'h0, 7'h20},
    {OP_IMM_OPCODE  , 3'h1, 7'h20},
    {OP_IMM_OPCODE  , 3'h2, 7'h20},
    {OP_IMM_OPCODE  , 3'h3, 7'h20},
    {OP_IMM_OPCODE  , 3'h4, 7'h20},
    {OP_IMM_OPCODE  , 3'h6, 7'h20},
    {OP_IMM_OPCODE  , 3'h7, 7'h20},
    {STORE_OPCODE   , 3'h3, 7'h00},
    {STORE_OPCODE   , 3'h4, 7'h00},
    {STORE_OPCODE   , 3'h5, 7'h00},
    {STORE_OPCODE   , 3'h6, 7'h00},
    {STORE_OPCODE   , 3'h7, 7'h00},
    {OP_OPCODE      , 3'h1, 7'h20},
    {OP_OPCODE      , 3'h2, 7'h20},
    {OP_OPCODE      , 3'h3, 7'h20},
    {OP_OPCODE      , 3'h4, 7'h20},
    {OP_OPCODE      , 3'h6, 7'h20},
    {OP_OPCODE      , 3'h7, 7'h20},
    {BRANCH_OPCODE  , 3'h2, 7'h00},
    {BRANCH_OPCODE  , 3'h3, 7'h00},
    {JALR_OPCODE    , 3'h1, 7'h00},
    {JALR_OPCODE    , 3'h2, 7'h00},
    {JALR_OPCODE    , 3'h3, 7'h00},
    {JALR_OPCODE    , 3'h4, 7'h00},
    {JALR_OPCODE    , 3'h5, 7'h00},
    {JALR_OPCODE    , 3'h6, 7'h00},
    {JALR_OPCODE    , 3'h7, 7'h00},
    {SYSTEM_OPCODE  , 3'h4, 7'h00}
  };

  initial begin
    $display("Test has been started");
    valid_instrs_direct_test();
    valid_instrs_random_test();
    illegal_instr_direct_test();
    illegal_instrs_random_test();

    $display("\nTest has been finished\nNumber of errors: %d\n", err_count);
    $finish();
    #5;
    $display("You're trying to run simulation that has finished. Aborting simulation.");
    $fatal();
  end

  function void randomize_with_given_opcode(input logic[4:0] given_opcode);
    if(!instr.randomize() with {(opcode == given_opcode);}) begin
      $fatal(1, "Can't ranomize instr with opcode == %0h", given_opcode);
    end
  endfunction

  task valid_instrs_direct_test();
    /*
      Enumeration of all possible instructions by every opcode, func3 and func7.
      Additionally, ecall, ebreak and mret instructions are generated manually.
    */
    foreach(valid_codes[i]) begin
      if(instr.randomize() with {(opcode == valid_codes[i][14:10]) && (func3 == valid_codes[i][9:7]) && (func7 == valid_codes[i][6:0]);}) begin
        @(posedge clk);
        fetched_instr_i <= instr.bits;
      end
      else begin
        $fatal(1, "Can't randomize instruction with opcode == %02h, func3 == %0h, func7 == %0h", valid_codes[i][14:10], valid_codes[i][9:7], valid_codes[i][6:0]);
      end
    end
    for(int i = 0; i < 3; i++) begin
      @(posedge clk);
      fetched_instr_i <= instr.system_instrs[i];
    end
  endtask

  task valid_instrs_random_test();
    /*
      A thousand random instructions for each opcode.
    */
    foreach(opcode_array[i]) begin
      repeat(1e3) begin
        randomize_with_given_opcode(opcode_array[i]);
        @(posedge clk);
        fetched_instr_i <= instr.bits;
      end
    end
  endtask

  task illegal_instr_direct_test();
  /*
    That's where real things are happening.
    This task is intent to check all the ways to get illegal_instr_o goes 1.
    Test trying:
    - incorrect low 2 bits on every opcode;
    - incorrect opcode;
    - incorrect func3 and func7 where it's possible;
    - incorrect fence, ecall, ebreak, mret instructions
  */
    incorrect_low_two_bits_test();
    incorrect_opcode_test();
    incorrect_func3_func7_test();
    incorrect_hardcode_instrs();
  endtask

  task incorrect_low_two_bits_test();
    /*
      For every opcode we generate a valid instruction and corrupt 2 low bits.
      So for every opcode we try 3 different instructions.
    */
    foreach(opcode_array[i]) begin
      for(int j = 0; j < 3; j++) begin
        randomize_with_given_opcode(opcode_array[i]);
        @(posedge clk);
        fetched_instr_i <= {instr.bits[31:2], j};
      end
    end
  endtask

  task incorrect_opcode_test();
    /*
      For every instruction type (every opcode for the simplicity sake) we try
      an instruction with incorrect opcode.
    */
    foreach(opcode_array[i]) begin
      automatic logic [4:0] incorrect_opcode;
      for(int j = 0; j < 3; j++) begin
        randomize_with_given_opcode(opcode_array[i]);
        @(posedge clk);
        assert(std::randomize(incorrect_opcode) with {!(incorrect_opcode inside {
                                                              LOAD_OPCODE,
                                                              MISC_MEM_OPCODE,
                                                              OP_IMM_OPCODE,
                                                              AUIPC_OPCODE,
                                                              STORE_OPCODE,
                                                              OP_OPCODE,
                                                              LUI_OPCODE,
                                                              BRANCH_OPCODE,
                                                              JALR_OPCODE,
                                                              JAL_OPCODE,
                                                              SYSTEM_OPCODE
                                                          });});
        fetched_instr_i <= {instr.bits[31:7], incorrect_opcode, 2'b11};
      end
    end
  endtask

  task incorrect_func3_func7_test();
    /*
      This test is opposite of valid_instrs_direct_test: we are looping through
      every illegal {opcode, func3, func7} combination and applying it onto
      generated instruction.
    */
    foreach(invalid_codes[i]) begin
      randomize_with_given_opcode(invalid_codes[i][14:10]);
      @(posedge clk);
      fetched_instr_i <= {invalid_codes[i][6:0], instr.bits[24:15], invalid_codes[i][9:7], instr.bits[11:7], invalid_codes[i][14:10], 2'b11};
    end
  endtask

  task incorrect_hardcode_instrs();
    /*
      In this test we try to broke fence, ecall, ebreak and mret instructions:
      - for the fence instr we need to make func3 to be not equal zero;
      - for ecall, ebreak and mret instructions we need to corrupt imm, rs1, rd
      values.
    */

    // Broken fence instructions
    for(int i = 1; i < 8; i++) begin
      randomize_with_given_opcode(MISC_MEM_OPCODE);
      @(posedge clk);
      fetched_instr_i <= {instr.bits[31:15], i, instr.bits[11:0]};
    end

    // Broken ecall, ebreak, mret instructions
    for(int j = 0; j < 3; j++) begin
      @(posedge clk);
      // broken imm field
      fetched_instr_i <= {12'd2, instr.system_instrs[j][19:0]};
      @(posedge clk);
      // broken rs1 field
      fetched_instr_i <= {instr.system_instrs[j][31:20], 5'd1, instr.system_instrs[j][14:0]};
      @(posedge clk);
      // broken rd field
      fetched_instr_i <= {instr.system_instrs[j][31:12], 5'd1, instr.system_instrs[j][6:0]};
    end
  endtask

  task illegal_instrs_random_test();
    /*
      It's inefficiently to randomize all 32 bits of instructions since most
      of them would be illegal by opcode or low 2 bits.
      This test will construct instructions from valid parts but in random order
      which will cause illegal instructions to be produced.
      Additionally test will insert illegal parts with low chance.
    */
    automatic logic [2:0] func3;
    automatic logic [6:0] func7;
    automatic logic [4:0] opcode;
    automatic logic [4:0] rs1, rs2, rd;
    automatic logic [1:0] low_bits;
    automatic logic [9:0] mutation;
    repeat(1e4) begin
      assert(std::randomize(mutation));
      // we want to broke (invert constraint of) func3 if
      // 9's bit is 1 while six lower bits are 0
      if(mutation[9] & !(|mutation[5:0])) begin
        assert(std::randomize(func7    ) with {!(func7 inside {7'h0, 7'h20});});
      end
      else begin
        assert(std::randomize(func7    ) with { (func7 inside {7'h0, 7'h20});});
      end
      if(mutation[8] & !(|mutation[5:0])) begin
        assert(std::randomize(opcode   ) with {!(opcode inside {
                                                                LOAD_OPCODE,
                                                                MISC_MEM_OPCODE,
                                                                OP_IMM_OPCODE,
                                                                AUIPC_OPCODE,
                                                                STORE_OPCODE,
                                                                OP_OPCODE,
                                                                LUI_OPCODE,
                                                                BRANCH_OPCODE,
                                                                JALR_OPCODE,
                                                                JAL_OPCODE,
                                                                SYSTEM_OPCODE
                                                              });});
      end
      else begin
        assert(std::randomize(opcode   ) with { (opcode inside {
                                                                LOAD_OPCODE,
                                                                MISC_MEM_OPCODE,
                                                                OP_IMM_OPCODE,
                                                                AUIPC_OPCODE,
                                                                STORE_OPCODE,
                                                                OP_OPCODE,
                                                                LUI_OPCODE,
                                                                BRANCH_OPCODE,
                                                                JALR_OPCODE,
                                                                JAL_OPCODE,
                                                                SYSTEM_OPCODE
                                                              });});
      end
      if(mutation[7] & !(|mutation[5:0])) begin
        assert(std::randomize(low_bits ) with {!(low_bits == 2'b11);});
      end
      else begin
        assert(std::randomize(low_bits ) with { (low_bits == 2'b11);});
      end
      assert(std::randomize(func3)); assert(std::randomize(rs1)); assert(std::randomize(rs2)); assert(std::randomize(rd));
      @(posedge clk);
      fetched_instr_i <= {func7, rs2, rs1, func3, rd, opcode, low_bits};
    end
  endtask

  bit test_paused_by_errs;
  initial begin
    clk                     = '0;
    err_count               = '0;
    test_paused_by_errs     = '0;
  end

  always #5 clk = ~clk;


  always @(posedge clk) begin
    if((err_count >= 10) & !test_paused_by_errs) begin
      test_paused_by_errs = '1;
      $display("\nTest has been stopped after 10 errors");
      $stop();
    end
  end

  logic [1:0]   a_sel_o;
  logic [2:0]   b_sel_o;
  logic [4:0]   alu_op_o;
  logic [2:0]   csr_op_o;
  logic         csr_we_o;
  logic         mem_req_o;
  logic         mem_we_o;
  logic [2:0]   mem_size_o;
  logic         gpr_we_o;
  logic [1:0]   wb_sel_o;
  logic         illegal_instr_o;
  logic         branch_o;
  logic         jal_o;
  logic         jalr_o;
  logic         mret_o;

  logic [1:0]   grm_a_sel_o;
  logic [2:0]   grm_b_sel_o;
  logic [4:0]   grm_alu_op_o;
  logic [2:0]   grm_csr_op_o;
  logic         grm_csr_we_o;
  logic         grm_mem_req_o;
  logic         grm_mem_we_o;
  logic [2:0]   grm_mem_size_o;
  logic         grm_gpr_we_o;
  logic [1:0]   grm_wb_sel_o;
  logic         grm_illegal_instr_o;
  logic         grm_branch_o;
  logic         grm_jal_o;
  logic         grm_jalr_o;
  logic         grm_mret_o;


  decoder DUT(.*);

  decoder_ref GRM(
    .fetched_instr_i  (fetched_instr_i    ),
    .a_sel_o          (grm_a_sel_o        ),
    .b_sel_o          (grm_b_sel_o        ),
    .alu_op_o         (grm_alu_op_o       ),
    .csr_op_o         (grm_csr_op_o       ),
    .csr_we_o         (grm_csr_we_o       ),
    .mem_req_o        (grm_mem_req_o      ),
    .mem_we_o         (grm_mem_we_o       ),
    .mem_size_o       (grm_mem_size_o     ),
    .gpr_we_o         (grm_gpr_we_o       ),
    .wb_sel_o         (grm_wb_sel_o       ),
    .illegal_instr_o  (grm_illegal_instr_o),
    .branch_o         (grm_branch_o       ),
    .jal_o            (grm_jal_o          ),
    .jalr_o           (grm_jalr_o         ),
    .mret_o           (grm_mret_o         )
  );

  logic [4:0] opcode;
  logic [2:0] func3;

  logic a_sel_check   ;
  logic b_sel_check   ;
  logic alu_op_check  ;
  logic csr_op_check  ;
  logic csr_we_check  ;
  logic mem_req_check ;
  logic mem_we_check  ;
  logic mem_size_check;
  logic gpr_we_check  ;
  logic wb_sel_check  ;
  logic branch_check  ;
  logic jal_check     ;
  logic jalr_check    ;
  logic mret_check    ;

  assign opcode         = fetched_instr_i[6:2];
  assign func3          = fetched_instr_i[14:12];

  assign a_sel_check    = !(opcode inside {MISC_MEM_OPCODE, SYSTEM_OPCODE});
  assign b_sel_check    = !(opcode inside {MISC_MEM_OPCODE, SYSTEM_OPCODE});
  assign alu_op_check   = !(opcode inside {MISC_MEM_OPCODE, SYSTEM_OPCODE});
  assign csr_op_check   =  (opcode == SYSTEM_OPCODE) && (func3 != 3'd0);
  assign csr_we_check   = 1'b1;
  assign mem_req_check  = 1'b1;
  assign mem_we_check   = 1'b1;
  assign mem_size_check =  (opcode inside {LOAD_OPCODE, STORE_OPCODE});
  assign gpr_we_check   = 1'b1;
    assign wb_sel_check   = !(opcode inside {STORE_OPCODE, MISC_MEM_OPCODE, BRANCH_OPCODE}) && (!(opcode == SYSTEM_OPCODE) | ((opcode == SYSTEM_OPCODE) & (func3 != 3'd0))); // (opcode == SYSTEM_OPCODE) -> (func3 != 3'd0)
  assign branch_check   = 1'b1;
  assign jal_check      = 1'b1;
  assign jalr_check     = 1'b1;
  assign mret_check     = 1'b1;

  string                     instr_str;
  string                     raw_instr;

  illegal_instr_prop: assert property(
    @(posedge clk)
    (grm_illegal_instr_o === illegal_instr_o)
  )
  else begin
    $display("illegal_instr_o value is incorrect (    %b instead of     %b), instruction: %s %s", illegal_instr_o, grm_illegal_instr_o , raw_instr, instr_str  );
    err_count++;
  end

  a_sel_prop   : assert property  (
    @(posedge clk) disable iff(grm_illegal_instr_o)
    a_sel_check    |-> (grm_a_sel_o    === a_sel_o   )
  )
  else begin
    $display("a_sel_o         value is incorrect (   %02b instead of    %02b), instruction: %s %s", a_sel_o   , grm_a_sel_o , raw_instr, instr_str  );
    err_count++;
  end

  b_sel_prop   : assert property  (
    @(posedge clk) disable iff(grm_illegal_instr_o)
    b_sel_check    |-> (grm_b_sel_o    === b_sel_o   )
  )
  else begin
    $display("b_sel_o         value is incorrect (  %03b instead of   %03b), instruction: %s %s", b_sel_o   , grm_b_sel_o , raw_instr, instr_str  );
    err_count++;
  end

  alu_op_prop  : assert property  (
    @(posedge clk) disable iff(grm_illegal_instr_o)
    alu_op_check   |-> (grm_alu_op_o   === alu_op_o  )
  )
  else begin
    $display("alu_op_o        value is incorrect (%05b instead of %05b), instruction: %s %s", alu_op_o  , grm_alu_op_o, raw_instr, instr_str  );
    err_count++;
  end

  csr_op_prop  : assert property  (
    @(posedge clk) disable iff(grm_illegal_instr_o)
    csr_op_check   |-> (grm_csr_op_o   === csr_op_o  )
  )
  else begin
    $display("csr_op_o        value is incorrect (  %03b instead of   %03b), instruction: %s %s", csr_op_o  , grm_csr_op_o, raw_instr, instr_str  );
    err_count++;
  end

  csr_we_prop  : assert property  (
    @(posedge clk)
    csr_we_check   |-> (grm_csr_we_o   === csr_we_o  )
  )
  else begin
    $display("csr_we_o        value is incorrect (    %b instead of     %b), instruction: %s %s", csr_we_o  , grm_csr_we_o, raw_instr, instr_str  );
    err_count++;
  end

  mem_req_prop : assert property  (
    @(posedge clk)
    mem_req_check  |-> (grm_mem_req_o  === mem_req_o )
  )
  else begin
    $display("mem_req_o       value is incorrect (    %b instead of     %b), instruction: %s %s", mem_req_o , grm_mem_req_o, raw_instr, instr_str );
    err_count++;
  end

  mem_we_prop  : assert property  (
    @(posedge clk)
    mem_we_check   |-> (grm_mem_we_o   === mem_we_o  )
  )
  else begin
    $display("mem_we_o        value is incorrect (    %b instead of     %b), instruction: %s %s", mem_we_o  , grm_mem_we_o, raw_instr, instr_str  );
    err_count++;
  end

  mem_size_prop: assert property  (
    @(posedge clk) disable iff(grm_illegal_instr_o)
    mem_size_check |-> (grm_mem_size_o === mem_size_o)
  )
  else begin
    $display("mem_size_o      value is incorrect (  %03b instead of   %03b), instruction: %s %s", mem_size_o, grm_mem_size_o, raw_instr, instr_str);
    err_count++;
  end

  gpr_we_prop  : assert property  (
    @(posedge clk)
    gpr_we_check   |-> (grm_gpr_we_o   === gpr_we_o  )
  )
  else begin
    $display("gpr_we_o        value is incorrect (    %b instead of     %b), instruction: %s %s", gpr_we_o  , grm_gpr_we_o, raw_instr, instr_str  );
    err_count++;
  end

  wb_sel_prop  : assert property  (
    @(posedge clk) disable iff(grm_illegal_instr_o)
    wb_sel_check   |-> (grm_wb_sel_o   === wb_sel_o  )
  )
  else begin
    $display("wb_sel_o        value is incorrect (   %b instead of    %b), instruction: %s %s", wb_sel_o  , grm_wb_sel_o, raw_instr, instr_str  );
    err_count++;
  end

  branch_prop  : assert property  (
    @(posedge clk)
    branch_check   |-> (grm_branch_o   === branch_o  )
  )
  else begin
    $display("branch_o        value is incorrect (    %b instead of     %b), instruction: %s %s", branch_o  , grm_branch_o, raw_instr, instr_str  );
    err_count++;
  end

  jal_prop     : assert property  (
    @(posedge clk)
    jal_check      |-> (grm_jal_o      === jal_o     )
  )
  else begin
    $display("jal_o           value is incorrect (    %b instead of     %b), instruction: %s %s", jal_o     , grm_jal_o   , raw_instr, instr_str  );
    err_count++;
  end

  jalr_prop    : assert property  (
    @(posedge clk)
    jalr_check     |-> (grm_jalr_o     === jalr_o    )
  )
  else begin
    $display("jalr_o          value is incorrect (    %b instead of     %b), instruction: %s %s", jalr_o    , grm_jalr_o  , raw_instr, instr_str  );
    err_count++;
  end

  mret_prop    : assert property  (
    @(posedge clk)
    mret_check     |-> (grm_mret_o     === mret_o    )
  )
  else begin
    $display("mret_o          value is incorrect (    %b instead of     %b), instruction: %s %s", mret_o    , grm_mret_o  , raw_instr, instr_str  );
    err_count++;
  end

  always_comb begin
    case (opcode)
      LUI_OPCODE, AUIPC_OPCODE, JAL_OPCODE:
        raw_instr = $sformatf("%020b %05b %07b   "           , fetched_instr_i[31:12], fetched_instr_i[11:7], fetched_instr_i[6:0]);
      JALR_OPCODE, LOAD_OPCODE, OP_IMM_OPCODE, SYSTEM_OPCODE:
        raw_instr = $sformatf("%012b %05b %03b %05b %07b "   , fetched_instr_i[31:20], fetched_instr_i[19:15], fetched_instr_i[14:12], fetched_instr_i[11:7], fetched_instr_i[6:0]);
      BRANCH_OPCODE, STORE_OPCODE, OP_OPCODE:
        raw_instr = $sformatf("%07b %05b %05b %03b %05b %07b", fetched_instr_i[31:25], fetched_instr_i[24:20], fetched_instr_i[19:15], fetched_instr_i[14:12], fetched_instr_i[11:7], fetched_instr_i[6:0]);
      MISC_MEM_OPCODE:
        raw_instr = $sformatf("%017b %03b %05b %07b  "       , fetched_instr_i[31:15], fetched_instr_i[14:12], fetched_instr_i[11:7], fetched_instr_i[6:0]);
      default:
        raw_instr = $sformatf("%032b     "                   , fetched_instr_i);
    endcase
  end

  always_comb begin
    if(&fetched_instr_i[1:0])
      case(opcode)
        LUI_OPCODE: begin
          instr_str = "(     LUI      )";
        end
        AUIPC_OPCODE: begin
          instr_str = "(    AUIPC     )";
        end
        JAL_OPCODE: begin
          instr_str = "(     JAL      )";
        end
        JALR_OPCODE: begin
          instr_str = func3? "( illegal_JALR )": "(     JALR     )";
        end
        BRANCH_OPCODE: begin
          case(func3)
            3'b000: instr_str = "(     BEQ      )";
            3'b001: instr_str = "(     BNE      )";
            3'b100: instr_str = "(     BLT      )";
            3'b101: instr_str = "(     BGE      )";
            3'b110: instr_str = "(     BLTU     )";
            3'b111: instr_str = "(     BGEU     )";
            default: instr_str= "(illegal_BRANCH)";
          endcase
        end
        LOAD_OPCODE: begin
          case(func3)
            3'b000: instr_str = "(      LB      )";
            3'b001: instr_str = "(      LH      )";
            3'b010: instr_str = "(      LW      )";
            3'b100: instr_str = "(      LBU     )";
            3'b101: instr_str = "(      LHU     )";
            default: instr_str= "( illegal_LOAD )";
          endcase
        end
        STORE_OPCODE: begin
          case(func3)
            3'b000: instr_str = "(      SB      )";
            3'b001: instr_str = "(      SH      )";
            3'b010: instr_str = "(      SW      )";
            default: instr_str = "(illegal_STORE)";
          endcase
        end
        OP_IMM_OPCODE: begin
          case({2'b0,func3})
            ALU_ADD  : instr_str = "(     ADDI     )";
            ALU_XOR  : instr_str = "(     XORI     )";
            ALU_OR   : instr_str = "(     ORI      )";
            ALU_AND  : instr_str = "(     ANDI     )";
            ALU_SRL  : instr_str = {fetched_instr_i[31],fetched_instr_i[29:25]}? "(illegal_OP_IMM)": fetched_instr_i[30]? "(     SRAI     )": "(     SRLI     )";
            ALU_SLL  : instr_str = fetched_instr_i[31:25]? "(illegal_OP_IMM)": "(     SLLI     )";
            ALU_SLTS : instr_str = "(     SLTI     )";
            ALU_SLTU : instr_str = "(    SLTIU     )";
            default   : instr_str = "(illegal_OP_IMM)";
          endcase
        end
        OP_OPCODE: begin
          if(!fetched_instr_i[29:25])
            case({fetched_instr_i[31:30], func3})
              ALU_ADD  : instr_str = "(      ADD     )";
              ALU_SUB  : instr_str = "(      SUB     )";
              ALU_XOR  : instr_str = "(      XOR     )";
              ALU_OR   : instr_str = "(      OR      )";
              ALU_AND  : instr_str = "(      AND     )";
              ALU_SRA  : instr_str = "(      SRA     )";
              ALU_SRL  : instr_str = "(      SRL     )";
              ALU_SLL  : instr_str = "(      SLL     )";
              ALU_SLTS : instr_str = "(      SLT     )";
              ALU_SLTU : instr_str = "(      SLTU    )";
              default  : instr_str = "(  illegal_OP  )";
            endcase
          else instr_str = "(  illegal_OP  )";
        end
        MISC_MEM_OPCODE: begin
          instr_str = func3 ? "(illegal_FENCE )": "(     FENCE    )";
        end
        SYSTEM_OPCODE: begin
          instr_str = "(illegal_SYSTEM)";
          case(func3)
            3'd0: begin
              case(fetched_instr_i)
                32'h000_0_0_0_73: instr_str = "(    ECALL     )";
                32'h001_0_0_0_73: instr_str = "(    EBREAK    )";
                32'h302_0_0_0_73: instr_str = "(    MRET      )";
              endcase
            end
            3'd1: instr_str = "(    CSRRW     )";
            3'd2: instr_str = "(    CSRRS     )";
            3'd3: instr_str = "(    CSRRC     )";
            3'd5: instr_str = "(    CSRRWI    )";
            3'd6: instr_str = "(    CSRRSI    )";
            3'd7: instr_str = "(    CSRRCI    )";
          endcase
        end
        default: instr_str = "(illegal_opcode)";
      endcase
    else instr_str = "(illegal_opcode)";
  end

  class riscv_instr;
    rand bit [20:0] imm;
    rand bit [ 6:0] func7;
    rand bit [ 4:0] shamt;
    rand bit [ 4:0] rs2;
    rand bit [ 4:0] rs1;
    rand bit [ 2:0] func3;
    rand bit [ 4:0] rd;
    rand bit [ 4:0] opcode;

    bit [31:0] bits;

    bit [31:0] system_instrs[3] = {
      32'h000_0_0_0_73, //ecall
      32'h001_0_0_0_73, //ebreak
      32'h302_0_0_0_73  //mret
    };

    constraint valid_opcode {opcode inside {  LOAD_OPCODE,
                                              MISC_MEM_OPCODE,
                                              OP_IMM_OPCODE,
                                              AUIPC_OPCODE,
                                              STORE_OPCODE,
                                              OP_OPCODE,
                                              LUI_OPCODE,
                                              BRANCH_OPCODE,
                                              JALR_OPCODE,
                                              JAL_OPCODE,
                                              SYSTEM_OPCODE
                                          };}

    constraint load_opcode      { (opcode == LOAD_OPCODE    )                                       -> !(func3 inside {3'h3, 3'h6, 3'h7});}

    constraint misc_mem_opcode  { (opcode == MISC_MEM_OPCODE)                                       ->  (func3 == 3'b000);}

    constraint op_imm_opcode1   {((opcode == OP_IMM_OPCODE  ) &&  (func3 == 3'h1))                  ->  (func7 == 7'h00);}
    constraint op_imm_opcode2   {((opcode == OP_IMM_OPCODE  ) &&  (func3 == 3'h5))                  ->  (func7 inside {7'h00, 7'h20});}

    constraint store_opcode     { (opcode == STORE_OPCODE   )                                       ->  (func3 inside {3'h0, 3'h1, 3'h2});}

    constraint op_opcode1       {((opcode == OP_OPCODE      ) &&  (func3 inside {3'b000, 3'b101}))  ->  (func7 inside {7'h00, 7'h20});}
    constraint op_opcode2       {((opcode == OP_OPCODE      ) && !(func3 inside {3'b000, 3'b101}))  ->  (func7 == 7'h00);}

    constraint branch_opcode    { (opcode == BRANCH_OPCODE  )                                       -> !(func3 inside {3'h2, 3'h3});}

    constraint jalr_opcode      { (opcode == JALR_OPCODE    )                                       ->  (func3 == 3'h0);}

    constraint system_opcode    { (opcode == SYSTEM_OPCODE  )                                       -> !(func3 == 3'h4);}

    function void post_randomize();
      case(opcode)
        LOAD_OPCODE, MISC_MEM_OPCODE, JALR_OPCODE: begin
          bits = {imm[11:0], rs1, func3, rd, opcode, 2'b11};
        end
        OP_IMM_OPCODE: begin
          if(func3 inside {3'h1, 3'h5}) begin
            bits = {func7, shamt, rs1, func3, rd, opcode, 2'b11};
          end
          else begin
            bits = {imm[11:0], rs1, func3, rd, opcode, 2'b11};
          end
        end
        AUIPC_OPCODE, LUI_OPCODE: begin
          bits = {imm, opcode, 2'b11};
        end
        STORE_OPCODE: begin
          bits = {imm[11:5], rs2, rs1, func3, imm[4:0], opcode, 2'b11};
        end
        OP_OPCODE: begin
          bits = {func7, rs2, rs1, func3, rd, opcode, 2'b11};
        end
        BRANCH_OPCODE: begin
          bits = {imm[12], imm[10:5], rs2, rs1, func3, imm[4:1], imm[11], opcode, 2'b11};
        end
        JAL_OPCODE: begin
          bits = {imm[20], imm[10:1], imm[11], imm[19:12], rd, opcode, 2'b11};
        end
        SYSTEM_OPCODE: begin
          if(func3 == 3'h0) begin
            bits = system_instrs[$urandom_range(3)];
          end
          else begin
            bits = {imm[11:0], rs1, func3, rd, opcode, 2'b11};
          end
        end
        default: begin
          $fatal(1, "Missing opcode %0h in post_randomize", opcode);
        end
      endcase
    endfunction

  endclass

endmodule

/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Alexey Kozin
* Email(s)       : @edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module gpr_we_table (gis_ew_rpg, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_ew_rpg;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_ew_rpg = 1'b1;
        5'b00001: gis_ew_rpg = 1'b0;
        5'b00010: gis_ew_rpg = 1'b0;
        5'b00011: gis_ew_rpg = 1'b0;
        5'b00100: gis_ew_rpg = 1'b1;
        5'b00101: gis_ew_rpg = 1'b1;
        5'b00110: gis_ew_rpg = 1'b0;
        5'b00111: gis_ew_rpg = 1'b0;
        5'b01000: gis_ew_rpg = 1'b0;
        5'b01001: gis_ew_rpg = 1'b0;
        5'b01010: gis_ew_rpg = 1'b0;
        5'b01011: gis_ew_rpg = 1'b0;
        5'b01100: gis_ew_rpg = 1'b1;
        5'b01101: gis_ew_rpg = 1'b1;
        5'b01110: gis_ew_rpg = 1'b0;
        5'b01111: gis_ew_rpg = 1'b0;
        5'b10000: gis_ew_rpg = 1'b0;
        5'b10001: gis_ew_rpg = 1'b0;
        5'b10010: gis_ew_rpg = 1'b0;
        5'b10011: gis_ew_rpg = 1'b0;
        5'b10100: gis_ew_rpg = 1'b0;
        5'b10101: gis_ew_rpg = 1'b0;
        5'b10110: gis_ew_rpg = 1'b0;
        5'b10111: gis_ew_rpg = 1'b0;
        5'b11000: gis_ew_rpg = 1'b0;
        5'b11001: gis_ew_rpg = 1'b1;
        5'b11010: gis_ew_rpg = 1'b0;
        5'b11011: gis_ew_rpg = 1'b1;
        5'b11100: gis_ew_rpg = 1'b1;
        5'b11101: gis_ew_rpg = 1'b0;
        5'b11110: gis_ew_rpg = 1'b0;
        5'b11111: gis_ew_rpg = 1'b0;
    endcase
endmodule

module csr_we_table (gis_ew_rsc, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_ew_rsc;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_ew_rsc = 1'b0;
        5'b00001: gis_ew_rsc = 1'b0;
        5'b00010: gis_ew_rsc = 1'b0;
        5'b00011: gis_ew_rsc = 1'b0;
        5'b00100: gis_ew_rsc = 1'b0;
        5'b00101: gis_ew_rsc = 1'b0;
        5'b00110: gis_ew_rsc = 1'b0;
        5'b00111: gis_ew_rsc = 1'b0;
        5'b01000: gis_ew_rsc = 1'b0;
        5'b01001: gis_ew_rsc = 1'b0;
        5'b01010: gis_ew_rsc = 1'b0;
        5'b01011: gis_ew_rsc = 1'b0;
        5'b01100: gis_ew_rsc = 1'b0;
        5'b01101: gis_ew_rsc = 1'b0;
        5'b01110: gis_ew_rsc = 1'b0;
        5'b01111: gis_ew_rsc = 1'b0;
        5'b10000: gis_ew_rsc = 1'b0;
        5'b10001: gis_ew_rsc = 1'b0;
        5'b10010: gis_ew_rsc = 1'b0;
        5'b10011: gis_ew_rsc = 1'b0;
        5'b10100: gis_ew_rsc = 1'b0;
        5'b10101: gis_ew_rsc = 1'b0;
        5'b10110: gis_ew_rsc = 1'b0;
        5'b10111: gis_ew_rsc = 1'b0;
        5'b11000: gis_ew_rsc = 1'b0;
        5'b11001: gis_ew_rsc = 1'b0;
        5'b11010: gis_ew_rsc = 1'b0;
        5'b11011: gis_ew_rsc = 1'b0;
        5'b11100: gis_ew_rsc = 1'b1;
        5'b11101: gis_ew_rsc = 1'b0;
        5'b11110: gis_ew_rsc = 1'b0;
        5'b11111: gis_ew_rsc = 1'b0;
    endcase
endmodule

module mem_req_table (gis_qer_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_qer_mem;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_qer_mem = 1'b1;
        5'b00001: gis_qer_mem = 1'b0;
        5'b00010: gis_qer_mem = 1'b0;
        5'b00011: gis_qer_mem = 1'b0;
        5'b00100: gis_qer_mem = 1'b0;
        5'b00101: gis_qer_mem = 1'b0;
        5'b00110: gis_qer_mem = 1'b0;
        5'b00111: gis_qer_mem = 1'b0;
        5'b01000: gis_qer_mem = 1'b1;
        5'b01001: gis_qer_mem = 1'b0;
        5'b01010: gis_qer_mem = 1'b0;
        5'b01011: gis_qer_mem = 1'b0;
        5'b01100: gis_qer_mem = 1'b0;
        5'b01101: gis_qer_mem = 1'b0;
        5'b01110: gis_qer_mem = 1'b0;
        5'b01111: gis_qer_mem = 1'b0;
        5'b10000: gis_qer_mem = 1'b0;
        5'b10001: gis_qer_mem = 1'b0;
        5'b10010: gis_qer_mem = 1'b0;
        5'b10011: gis_qer_mem = 1'b0;
        5'b10100: gis_qer_mem = 1'b0;
        5'b10101: gis_qer_mem = 1'b0;
        5'b10110: gis_qer_mem = 1'b0;
        5'b10111: gis_qer_mem = 1'b0;
        5'b11000: gis_qer_mem = 1'b0;
        5'b11001: gis_qer_mem = 1'b0;
        5'b11010: gis_qer_mem = 1'b0;
        5'b11011: gis_qer_mem = 1'b0;
        5'b11100: gis_qer_mem = 1'b0;
        5'b11101: gis_qer_mem = 1'b0;
        5'b11110: gis_qer_mem = 1'b0;
        5'b11111: gis_qer_mem = 1'b0;
    endcase
endmodule

module mem_we_table (gis_ew_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_ew_mem;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_ew_mem = 1'b0;
        5'b00001: gis_ew_mem = 1'b0;
        5'b00010: gis_ew_mem = 1'b0;
        5'b00011: gis_ew_mem = 1'b0;
        5'b00100: gis_ew_mem = 1'b0;
        5'b00101: gis_ew_mem = 1'b0;
        5'b00110: gis_ew_mem = 1'b0;
        5'b00111: gis_ew_mem = 1'b0;
        5'b01000: gis_ew_mem = 1'b1;
        5'b01001: gis_ew_mem = 1'b0;
        5'b01010: gis_ew_mem = 1'b0;
        5'b01011: gis_ew_mem = 1'b0;
        5'b01100: gis_ew_mem = 1'b0;
        5'b01101: gis_ew_mem = 1'b0;
        5'b01110: gis_ew_mem = 1'b0;
        5'b01111: gis_ew_mem = 1'b0;
        5'b10000: gis_ew_mem = 1'b0;
        5'b10001: gis_ew_mem = 1'b0;
        5'b10010: gis_ew_mem = 1'b0;
        5'b10011: gis_ew_mem = 1'b0;
        5'b10100: gis_ew_mem = 1'b0;
        5'b10101: gis_ew_mem = 1'b0;
        5'b10110: gis_ew_mem = 1'b0;
        5'b10111: gis_ew_mem = 1'b0;
        5'b11000: gis_ew_mem = 1'b0;
        5'b11001: gis_ew_mem = 1'b0;
        5'b11010: gis_ew_mem = 1'b0;
        5'b11011: gis_ew_mem = 1'b0;
        5'b11100: gis_ew_mem = 1'b0;
        5'b11101: gis_ew_mem = 1'b0;
        5'b11110: gis_ew_mem = 1'b0;
        5'b11111: gis_ew_mem = 1'b0;
    endcase
endmodule

module branch_table (gis_hcnarb, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_hcnarb;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_hcnarb = 1'b0;
        5'b00001: gis_hcnarb = 1'b0;
        5'b00010: gis_hcnarb = 1'b0;
        5'b00011: gis_hcnarb = 1'b0;
        5'b00100: gis_hcnarb = 1'b0;
        5'b00101: gis_hcnarb = 1'b0;
        5'b00110: gis_hcnarb = 1'b0;
        5'b00111: gis_hcnarb = 1'b0;
        5'b01000: gis_hcnarb = 1'b0;
        5'b01001: gis_hcnarb = 1'b0;
        5'b01010: gis_hcnarb = 1'b0;
        5'b01011: gis_hcnarb = 1'b0;
        5'b01100: gis_hcnarb = 1'b0;
        5'b01101: gis_hcnarb = 1'b0;
        5'b01110: gis_hcnarb = 1'b0;
        5'b01111: gis_hcnarb = 1'b0;
        5'b10000: gis_hcnarb = 1'b0;
        5'b10001: gis_hcnarb = 1'b0;
        5'b10010: gis_hcnarb = 1'b0;
        5'b10011: gis_hcnarb = 1'b0;
        5'b10100: gis_hcnarb = 1'b0;
        5'b10101: gis_hcnarb = 1'b0;
        5'b10110: gis_hcnarb = 1'b0;
        5'b10111: gis_hcnarb = 1'b0;
        5'b11000: gis_hcnarb = 1'b1;
        5'b11001: gis_hcnarb = 1'b0;
        5'b11010: gis_hcnarb = 1'b0;
        5'b11011: gis_hcnarb = 1'b0;
        5'b11100: gis_hcnarb = 1'b0;
        5'b11101: gis_hcnarb = 1'b0;
        5'b11110: gis_hcnarb = 1'b0;
        5'b11111: gis_hcnarb = 1'b0;
    endcase
endmodule

module jalr_table (gis_rlaj, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_rlaj;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_rlaj = 1'b0;
        5'b00001: gis_rlaj = 1'b0;
        5'b00010: gis_rlaj = 1'b0;
        5'b00011: gis_rlaj = 1'b0;
        5'b00100: gis_rlaj = 1'b0;
        5'b00101: gis_rlaj = 1'b0;
        5'b00110: gis_rlaj = 1'b0;
        5'b00111: gis_rlaj = 1'b0;
        5'b01000: gis_rlaj = 1'b0;
        5'b01001: gis_rlaj = 1'b0;
        5'b01010: gis_rlaj = 1'b0;
        5'b01011: gis_rlaj = 1'b0;
        5'b01100: gis_rlaj = 1'b0;
        5'b01101: gis_rlaj = 1'b0;
        5'b01110: gis_rlaj = 1'b0;
        5'b01111: gis_rlaj = 1'b0;
        5'b10000: gis_rlaj = 1'b0;
        5'b10001: gis_rlaj = 1'b0;
        5'b10010: gis_rlaj = 1'b0;
        5'b10011: gis_rlaj = 1'b0;
        5'b10100: gis_rlaj = 1'b0;
        5'b10101: gis_rlaj = 1'b0;
        5'b10110: gis_rlaj = 1'b0;
        5'b10111: gis_rlaj = 1'b0;
        5'b11000: gis_rlaj = 1'b0;
        5'b11001: gis_rlaj = 1'b1;
        5'b11010: gis_rlaj = 1'b0;
        5'b11011: gis_rlaj = 1'b0;
        5'b11100: gis_rlaj = 1'b0;
        5'b11101: gis_rlaj = 1'b0;
        5'b11110: gis_rlaj = 1'b0;
        5'b11111: gis_rlaj = 1'b0;
    endcase
endmodule

module decoder_ref (
    input  logic [31:0] fetched_instr_i,
    output logic [1:0]  a_sel_o,
    output logic [2:0]  b_sel_o,
    output logic [4:0]  alu_op_o,
    output logic [2:0]  csr_op_o,
    output logic        csr_we_o,
    output logic        mem_req_o,
    output logic        mem_we_o,
    output logic [2:0]  mem_size_o,
    output logic        gpr_we_o,
    output logic [1:0]  wb_sel_o,
    output logic        illegal_instr_o,
    output logic        branch_o,
    output logic        jal_o,
    output logic        jalr_o,
    output logic        mret_o
);

    logic [4:0] epyt_r;
    logic [4:0] htira_epyt_i;
    logic [4:0] daol_epyt_i;
    logic [4:0] rlaj_epyt_i;
    logic [4:0] ecnef_epyt_i;
    logic [4:0] rsc_epyt_i;
    logic [4:0] epyt_s;
    logic [4:0] epyt_b;
    logic [4:0] iul_epyt_u;
    logic [4:0] cpiua_epyt_u;
    logic [4:0] epyt_j;

    logic [4:0] edocpo;
    logic [1:0] bsl;
    logic [6:0] tcnuf_7;
    logic [2:0] tcnuf_3;

    logic       po_dda;
    logic       po_bus;
    logic       po_rox;
    logic       po_ro;
    logic       po_dna;
    logic       po_lls;
    logic       po_lrs;
    logic       po_ars;
    logic       po_tls;
    logic       po_utls;
    logic       po_idda;
    logic       po_irox;
    logic       po_iro;
    logic       po_idna;
    logic       po_ills;
    logic       po_ilrs;
    logic       po_iars;
    logic       po_itls;
    logic       po_uitls;
    logic       po_bl;
    logic       po_hl;
    logic       po_wl;
    logic       po_ubl;
    logic       po_uhl;
    logic       po_bs;
    logic       po_hs;
    logic       po_ws;
    logic       po_qeb;
    logic       po_enb;
    logic       po_tlb;
    logic       po_egb;
    logic       po_utlb;
    logic       po_uegb;
    logic       po_laj;
    logic       po_rlaj;
    logic       po_iul;
    logic       po_cpiua;
    logic       po_ecnef;
    logic       po_llace;
    logic       po_kaerbe;
    logic       po_term;
    logic       po_wrssc;
    logic       po_srssc;
    logic       po_crssc;
    logic       po_iwrssc;
    logic       po_isrssc;
    logic       po_icrssc;

    logic       po_htira;
    logic       po_mmi;
    logic       po_daol;
    logic       po_erots;
    logic       po_hcnarb;
    logic       po_vne;
    logic       po_rsc;

    logic gis_ew_rsc;
    logic gis_ew_rsc_erp;
    logic gis_qer_mem;
    logic gis_ew_mem;
    logic gis_ew_rpg;
    logic gis_ew_rpg_erp;
    logic gis_hcnarb;
    logic gis_rlaj;

    csr_we_table  block_a (gis_ew_rsc_erp, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    mem_req_table block_b (gis_qer_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    mem_we_table  block_c (gis_ew_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    gpr_we_table  block_d (gis_ew_rpg_erp, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    branch_table  block_e (gis_hcnarb, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    jalr_table    block_f (gis_rlaj, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);

    assign gis_ew_rsc = gis_ew_rsc_erp & !illegal_instr_o & !po_term;
    assign gis_ew_rpg = gis_ew_rpg_erp & !illegal_instr_o & !po_term;

    assign epyt_r       = 5'b01100;
    assign htira_epyt_i = 5'b00100;
    assign daol_epyt_i  = 5'b00000;
    assign rlaj_epyt_i  = 5'b11001;
    assign ecnef_epyt_i = 5'b00011;
    assign rsc_epyt_i   = 5'b11100;
    assign epyt_s       = 5'b01000;
    assign epyt_b       = 5'b11000;
    assign iul_epyt_u   = 5'b01101;
    assign cpiua_epyt_u = 5'b00101;
    assign epyt_j       = 5'b11011;

    assign edocpo = fetched_instr_i[6:2];
    assign edocpo_6 = fetched_instr_i[6];
    assign edocpo_5 = fetched_instr_i[5];
    assign edocpo_4 = fetched_instr_i[4];
    assign edocpo_3 = fetched_instr_i[3];
    assign edocpo_2 = fetched_instr_i[2];
    assign bsl    = fetched_instr_i[1:0];
    assign tcnuf_7 = fetched_instr_i[31:25];
    assign tcnuf_3 = fetched_instr_i[14:12];

    assign po_dda    = edocpo == epyt_r       & tcnuf_3 == 'h0 & tcnuf_7 == 'h00;
    assign po_bus    = edocpo == epyt_r       & tcnuf_3 == 'h0 & tcnuf_7 == 'h20;
    assign po_rox    = edocpo == epyt_r       & tcnuf_3 == 'h4 & tcnuf_7 == 'h00;
    assign po_ro     = edocpo == epyt_r       & tcnuf_3 == 'h6 & tcnuf_7 == 'h00;
    assign po_dna    = edocpo == epyt_r       & tcnuf_3 == 'h7 & tcnuf_7 == 'h00;
    assign po_lls    = edocpo == epyt_r       & tcnuf_3 == 'h1 & tcnuf_7 == 'h00;
    assign po_lrs    = edocpo == epyt_r       & tcnuf_3 == 'h5 & tcnuf_7 == 'h00;
    assign po_ars    = edocpo == epyt_r       & tcnuf_3 == 'h5 & tcnuf_7 == 'h20;
    assign po_tls    = edocpo == epyt_r       & tcnuf_3 == 'h2 & tcnuf_7 == 'h00;
    assign po_utls   = edocpo == epyt_r       & tcnuf_3 == 'h3 & tcnuf_7 == 'h00;

    assign po_idda   = edocpo == htira_epyt_i & tcnuf_3 == 'h0                 ;
    assign po_irox   = edocpo == htira_epyt_i & tcnuf_3 == 'h4                 ;
    assign po_iro    = edocpo == htira_epyt_i & tcnuf_3 == 'h6                 ;
    assign po_idna   = edocpo == htira_epyt_i & tcnuf_3 == 'h7                 ;
    assign po_ills   = edocpo == htira_epyt_i & tcnuf_3 == 'h1 & tcnuf_7 == 'h00;
    assign po_ilrs   = edocpo == htira_epyt_i & tcnuf_3 == 'h5 & tcnuf_7 == 'h00;
    assign po_iars   = edocpo == htira_epyt_i & tcnuf_3 == 'h5 & tcnuf_7 == 'h20;
    assign po_itls   = edocpo == htira_epyt_i & tcnuf_3 == 'h2                 ;
    assign po_uitls  = edocpo == htira_epyt_i & tcnuf_3 == 'h3                 ;

    assign po_bl     = edocpo == daol_epyt_i  & tcnuf_3 == 'h0                 ;
    assign po_hl     = edocpo == daol_epyt_i  & tcnuf_3 == 'h1                 ;
    assign po_wl     = edocpo == daol_epyt_i  & tcnuf_3 == 'h2                 ;
    assign po_ubl    = edocpo == daol_epyt_i  & tcnuf_3 == 'h4                 ;
    assign po_uhl    = edocpo == daol_epyt_i  & tcnuf_3 == 'h5                 ;

    assign po_bs     = edocpo == epyt_s       & tcnuf_3 == 'h0                 ;
    assign po_hs     = edocpo == epyt_s       & tcnuf_3 == 'h1                 ;
    assign po_ws     = edocpo == epyt_s       & tcnuf_3 == 'h2                 ;

    assign po_qeb    = edocpo == epyt_b       & tcnuf_3 == 'h0                 ;
    assign po_enb    = edocpo == epyt_b       & tcnuf_3 == 'h1                 ;
    assign po_tlb    = edocpo == epyt_b       & tcnuf_3 == 'h4                 ;
    assign po_egb    = edocpo == epyt_b       & tcnuf_3 == 'h5                 ;
    assign po_utlb   = edocpo == epyt_b       & tcnuf_3 == 'h6                 ;
    assign po_uegb   = edocpo == epyt_b       & tcnuf_3 == 'h7                 ;

    assign po_laj    = edocpo == epyt_j                                       ;

    assign po_rlaj   = edocpo == rlaj_epyt_i  & tcnuf_3 == 'h0                 ;

    assign po_iul    = edocpo == iul_epyt_u                                   ;

    assign po_cpiua  = edocpo == cpiua_epyt_u                                 ;

    assign po_ecnef  = edocpo == ecnef_epyt_i & tcnuf_3 == 'h0                 ;

    assign po_llace  = fetched_instr_i == 32'h00000073;
    assign po_kaerbe = fetched_instr_i == 32'h00100073;

    assign po_term   = fetched_instr_i == 32'h30200073;

    assign po_wrssc  = edocpo == rsc_epyt_i   & tcnuf_3 == 'h1                 ;
    assign po_srssc  = edocpo == rsc_epyt_i   & tcnuf_3 == 'h2                 ;
    assign po_crssc  = edocpo == rsc_epyt_i   & tcnuf_3 == 'h3                 ;
    assign po_iwrssc = edocpo == rsc_epyt_i   & tcnuf_3 == 'h5                 ;
    assign po_isrssc = edocpo == rsc_epyt_i   & tcnuf_3 == 'h6                 ;
    assign po_icrssc = edocpo == rsc_epyt_i   & tcnuf_3 == 'h7                 ;

    assign po_htira  = po_dda | po_bus | po_rox | po_ro | po_dna | po_lls | po_lrs | po_ars | po_tls | po_utls;
    assign po_mmi    = po_idda | po_irox | po_iro | po_idna | po_ills | po_ilrs | po_iars | po_itls | po_uitls;
    assign po_daol   = po_bl | po_hl | po_wl | po_ubl | po_uhl;
    assign po_erots  = po_bs | po_hs | po_ws;
    assign po_hcnarb = po_qeb | po_enb | po_tlb | po_egb | po_utlb | po_uegb;
    assign po_vne    = po_llace | po_kaerbe;
    assign po_rsc    = po_wrssc | po_srssc | po_crssc | po_iwrssc | po_isrssc | po_icrssc;

    always_comb begin
        if (bsl == 2'b11) begin
            if (po_htira) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = po_dda  ? 5'b00000 :
                                po_bus  ? 5'b01000 :
                                po_rox  ? 5'b00100 :
                                po_ro   ? 5'b00110 :
                                po_dna  ? 5'b00111 :
                                po_lls  ? 5'b00001 :
                                po_lrs  ? 5'b00101 :
                                po_ars  ? 5'b01101 :
                                po_tls  ? 5'b00010 :
                                po_utls ? 5'b00011 :
                                            5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_mmi) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b001;
                alu_op_o        = po_idda  ? 5'b00000 :
                                po_irox  ? 5'b00100 :
                                po_iro   ? 5'b00110 :
                                po_idna  ? 5'b00111 :
                                po_ills  ? 5'b00001 :
                                po_ilrs  ? 5'b00101 :
                                po_iars  ? 5'b01101 :
                                po_itls  ? 5'b00010 :
                                po_uitls ? 5'b00011 :
                                            5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_daol) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b001;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = 1'b0;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = tcnuf_3;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b01;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_erots) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b011;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = tcnuf_3;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_hcnarb) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = po_qeb  ? 5'b11000 :
                                po_enb  ? 5'b11001 :
                                po_tlb  ? 5'b11100 :
                                po_egb  ? 5'b11101 :
                                po_utlb ? 5'b11110 :
                                po_uegb ? 5'b11111 :
                                            5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_laj) begin
                a_sel_o         = 2'b01;
                b_sel_o         = 3'b100;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b1;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_rlaj) begin
                a_sel_o         = 2'b01;
                b_sel_o         = 3'b100;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_iul) begin
                a_sel_o         = 2'b10;
                b_sel_o         = 3'b010;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_cpiua) begin
                a_sel_o         = 2'b01;
                b_sel_o         = 3'b010;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_ecnef) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_vne) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b1;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_term) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b1;
            end
            else if (po_rsc) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = tcnuf_3;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b10;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = 1'b0;
                mem_req_o       = 1'b0;
                mem_we_o        = 1'b0;
                mem_size_o      = 3'b011;
                gpr_we_o        = 1'b0;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b1;
                branch_o        = 1'b0;
                jal_o           = 1'b0;
                jalr_o          = 1'b0;
                mret_o          = 1'b0;
            end
        end
        else begin
            a_sel_o         = 2'b00;
            b_sel_o         = 3'b000;
            alu_op_o        = 5'b00000;
            csr_op_o        = 3'b000;
            csr_we_o        = 1'b0;
            mem_req_o       = 1'b0;
            mem_we_o        = 1'b0;
            mem_size_o      = 3'b011;
            gpr_we_o        = 1'b0;
            wb_sel_o        = 2'b00;
            illegal_instr_o = 1'b1;
            branch_o        = 1'b0;
            jal_o           = 1'b0;
            jalr_o          = 1'b0;
            mret_o          = 1'b0;
        end
    end

endmodule
