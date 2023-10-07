`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
// 
// Create Date:    
// Design Name: 
// Module Name:    tb_decoder_riscv
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: tb for decoder riscv
// 
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

module tb_decoder_riscv();

  import riscv_pkg::*;
  parameter delay = 4;
  parameter cycle = 200; // per one opcode

  reg   [31:0]               instr;
  wire  [1:0]                a_sel;
  wire  [2:0]                b_sel;
  wire  [ALU_OP_WIDTH-1:0]   alu_op;
  wire  [2:0]                csr_op;
  wire                       csr_we;
  wire                       mem_req;
  wire                       mem_we;
  wire  [2:0]                mem_size;
  wire                       gpr_we;
  wire  [1:0]                wb_sel;
  wire                       illegal_instr;
  wire                       branch;
  wire                       jal;
  wire                       jalr;
  wire                       mret;

  reg                        a_sel_miss;
  reg                        b_sel_miss;
  reg                        alu_op_miss;
  reg                        csr_op_miss;
  reg                        csr_we_miss;
  reg                        mem_req_miss;
  reg                        mem_we_miss;
  reg                        mem_size_miss;
  reg                        gpr_we_miss;
  reg                        wb_sel_miss;
  reg                        illegal_miss;
  reg                        branch_miss;
  reg                        jal_miss;
  reg                        jalr_miss;
  reg                        mret_miss;

  string                     opcode_type;
  string                     instr_type;

  decoder_riscv dut (
    .fetched_instr_i  (instr),
    .a_sel_o          (a_sel),
    .b_sel_o          (b_sel),
    .alu_op_o         (alu_op),
    .csr_op_o         (csr_op),
    .csr_we_o         (csr_we),
    .mem_req_o        (mem_req),
    .mem_we_o         (mem_we),
    .mem_size_o       (mem_size),
    .gpr_we_o         (gpr_we),
    .wb_sel_o         (wb_sel),
    .illegal_instr_o  (illegal_instr),
    .branch_o         (branch),
    .jal_o            (jal),
    .jalr_o           (jalr),
    .mret_o           (mret)
  );
  
  decoder_riscv_ref grm(.fetched_instr_i  (instr));

  wire [4:0] opcode;
  assign opcode = instr[6:2];

  always @(*) begin
    case (opcode)
      LUI_OPCODE, AUIPC_OPCODE, JAL_OPCODE:
        instr_type = $sformatf("%020b %05b %07b   ", instr[31:12], instr[11:7], instr[6:0]);
      JALR_OPCODE, LOAD_OPCODE, OP_IMM_OPCODE, SYSTEM_OPCODE:
        instr_type = $sformatf("%012b %05b %03b %05b %07b ", instr[31:20], instr[19:15], instr[14:12], instr[11:7], instr[6:0]);
      BRANCH_OPCODE, STORE_OPCODE, OP_OPCODE:
        instr_type = $sformatf("%07b %05b %05b %03b %05b %07b", instr[31:25], instr[24:20], instr[19:15], instr[14:12], instr[11:7], instr[6:0]);
      MISC_MEM_OPCODE: 
        instr_type = $sformatf("%017b %03b %05b %07b  ", instr[31:15], instr[14:12], instr[11:7], instr[6:0]);
      default: 
        instr_type = $sformatf("%032b     ", instr);
    endcase
  end

  always @(*) begin
    a_sel_miss      = 'b0;
    b_sel_miss      = 'b0;
    alu_op_miss     = 'b0;
    csr_op_miss     = 'b0;
    csr_we_miss     = 'b0;
    mem_req_miss    = 'b0;
    mem_we_miss     = 'b0;
    mem_size_miss   = 'b0;
    gpr_we_miss   = 'b0;
    wb_sel_miss = 'b0;
    illegal_miss    = 'b0;
    branch_miss     = 'b0;
    jal_miss        = 'b0;
    jalr_miss       = 'b0;
    mret_miss       = 'b0;
    case (opcode)
      LOAD_OPCODE, STORE_OPCODE:
      begin
        a_sel_miss      = (grm.a_sel_o !== a_sel) & !illegal_instr;
        b_sel_miss      = (grm.b_sel_o !== b_sel) & !illegal_instr;
        alu_op_miss     = (grm.alu_op_o !== alu_op) & !illegal_instr;
        csr_we_miss     = (grm.csr_we_o !== csr_we);
        mem_req_miss    = grm.mem_req_o !== mem_req;
        mem_we_miss     = grm.mem_we_o !== mem_we;
        mem_size_miss   = (grm.mem_size_o !== mem_size) & !illegal_instr;
        gpr_we_miss   = grm.gpr_we_o !== gpr_we;
        wb_sel_miss = (grm.wb_sel_o !== wb_sel) & !illegal_instr;
        illegal_miss    = grm.illegal_instr_o !== illegal_instr;
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end

      JAL_OPCODE, JALR_OPCODE,
      AUIPC_OPCODE, 
      OP_IMM_OPCODE, OP_OPCODE:
      begin
        a_sel_miss      = (grm.a_sel_o !== a_sel) & !illegal_instr;
        b_sel_miss      = (grm.b_sel_o !== b_sel) & !illegal_instr;
        alu_op_miss     = (grm.alu_op_o !== alu_op) & !illegal_instr;
        csr_we_miss     = (grm.csr_we_o !== csr_we);
        mem_req_miss    = grm.mem_req_o !== mem_req;
        mem_we_miss     = grm.mem_we_o !== mem_we;
        //mem_size_miss   = (grm.mem_size_o !== mem_size) & !illegal_instr;
        gpr_we_miss   = grm.gpr_we_o !== gpr_we;
        wb_sel_miss = (grm.wb_sel_o !== wb_sel) & !illegal_instr;
        illegal_miss    = grm.illegal_instr_o !== illegal_instr;
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end
      
      BRANCH_OPCODE: 
      begin
        a_sel_miss      = (grm.a_sel_o !== a_sel) & !illegal_instr;
        b_sel_miss      = (grm.b_sel_o !== b_sel) & !illegal_instr;
        alu_op_miss     = (grm.alu_op_o !== alu_op) & !illegal_instr;
        csr_we_miss     = (grm.csr_we_o !== csr_we);
        mem_req_miss    = grm.mem_req_o !== mem_req;
        mem_we_miss     = grm.mem_we_o !== mem_we;
        //mem_size_miss   = (grm.mem_size_o !== mem_size) & !illegal_instr;
        gpr_we_miss   = grm.gpr_we_o !== gpr_we;
        //wb_sel_miss = (grm.wb_sel_o !== wb_sel) & !illegal_instr;
        illegal_miss    = grm.illegal_instr_o !== illegal_instr;
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end

      LUI_OPCODE: begin
        a_sel_miss      = (grm.a_sel_o !== a_sel) & !illegal_instr;
        b_sel_miss      = (grm.b_sel_o !== b_sel) & !illegal_instr;
        alu_op_miss     = ((alu_op !== ALU_ADD)&(alu_op !== ALU_XOR)&(alu_op !== ALU_OR)) & !illegal_instr;
        csr_we_miss     = (grm.csr_we_o !== csr_we);
        mem_req_miss    = grm.mem_req_o !== mem_req;
        mem_we_miss     = grm.mem_we_o !== mem_we;
        //mem_size_miss   = (grm.mem_size_o !== mem_size) & !illegal_instr;
        gpr_we_miss   = grm.gpr_we_o !== gpr_we;
        wb_sel_miss = (grm.wb_sel_o !== wb_sel) & !illegal_instr;
        illegal_miss    = grm.illegal_instr_o !== illegal_instr;
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end
      
      SYSTEM_OPCODE: csr_op_miss     = (grm.csr_op_o !== csr_op);
      
      default:      //MISC_MEM_OPCODE, SYSTEM_OPCODE and other
      begin
        //a_sel_miss      = grm.a_sel_o !== a_sel;
        //b_sel_miss      = grm.b_sel_o !== b_sel;
        //alu_op_miss     = grm.alu_op_o !== alu_op;
        csr_we_miss     = (grm.csr_we_o !== csr_we);
        mem_req_miss    = grm.mem_req_o !== mem_req;
        mem_we_miss     = grm.mem_we_o !== mem_we;
        //mem_size_miss   = grm.mem_size_o !== mem_size;
        gpr_we_miss   = grm.gpr_we_o !== gpr_we;
        //wb_sel_miss = grm.wb_sel_o !== wb_sel;
        illegal_miss    = grm.illegal_instr_o !== illegal_instr;
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end
    endcase
  end

  reg [4:0] X;
  reg [$clog2(cycle+1)-1:0] V;
  integer error;

  initial begin
    $timeformat(-9, 2, " ns", 3);
    error = 0;
  end

  initial begin
    $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
    
    for (V=0; V<cycle/10; V=V+1) begin  // illegal по 11 в конце opcode
        instr[1:0]  = $random;
        instr[6:2]  = {1'b0,V[1:0],2'b0};
        instr[31:7] = 'b0;
        #delay;
    end
    for (V=0; V<cycle; V=V+1) begin  // illegal по OP_OPCODE funct7
        instr[11:0]  = {5'b0,OP_OPCODE,2'b11};
        instr[14:12] = V;
        instr[24:15] = $random;
        instr[31:25] = 2**($random % 7);
        #delay;
    end
    for (V=0; V<cycle; V=V+1) begin  // illegal по SYSTEM_OPCODE
        instr[6:0]  = {SYSTEM_OPCODE,2'b11};
        instr[31:7] = 2**($random % 25);
        #delay;
    end
    instr[6:0]  = {SYSTEM_OPCODE,2'b11};
    instr[31:7] = 25'h604000;
    #delay;
    $stop();
    for (X=0; X<2**5-1; X=X+1) begin
      for (V=0; V<cycle; V=V+1) begin
        instr[1:0]  = 2'b11;
        instr[6:2]  = X;
        instr[31:7] = $random;
        #delay;
      end
    end
    for (V=0; V<cycle; V=V+1) begin
      instr = $random;
      #delay;
    end

    if (|error)
      $display ("FAIL!\nThere are errors in the design, number of errors: %d", error);
    else
      $display ("\ndecoder SUCCESS!!!\n");
    $finish;
  end

  always begin
    @(instr);
    #2;
    if (illegal_miss)begin
      $display("Output 'illegal_instr_o' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",illegal_instr, grm.illegal_instr_o, instr_type, opcode_type, $time);
      error = error + 1'b1;
      end
    if (~illegal_miss) begin
      if(!illegal_instr) begin
          if (a_sel_miss)begin
            $display ("Output 'a_sel_o  ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",a_sel, grm.a_sel_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
            end
          if (b_sel_miss)begin
            $display ("Output 'b_sel_o  ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",b_sel, grm.b_sel_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
            end
          if (alu_op_miss)begin
            $display ("Output 'alu_op_o       ' is incorrect(%b instead of %b), instruction: %s %s, time: %t",alu_op, grm.alu_op_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
            end
          if (csr_op_miss) begin
            $display ("Output 'csr_op_o       ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",csr_op, grm.csr_op_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
          end
          if (mem_size_miss)begin
            $display ("Output 'mem_size_o     ' is incorrect( %b  instead of %b  ), instruction: %s %s, time: %t",mem_size, grm.mem_size_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
          end
          if (wb_sel_miss)begin
            $display ("Output 'wb_sel_o   ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",wb_sel, grm.wb_sel_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
          end
      end
      if (csr_we_miss) begin
        $display ("Output 'csr_we_o       ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",csr_we, grm.csr_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
      end
      if (mem_we_miss)begin
        $display ("Output 'mem_we_o       ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",mem_we, grm.mem_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (mem_req_miss)begin
        $display ("Output 'mem_req_o      ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",mem_req, grm.mem_req_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (gpr_we_miss)begin
        $display ("Output 'gpr_we_o     ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",gpr_we, grm.gpr_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (branch_miss)begin
        $display ("Output 'branch_o       ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",branch, grm.branch_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (jal_miss)begin
        $display ("Output 'jal_o          ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",jal, grm.jal_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (jalr_miss)begin
        $display ("Output 'jalr_o         ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",jalr, grm.jalr_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (mret_miss)begin
        $display ("Output 'mret_o         ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",mret, grm.mret_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
    end

  end
  
  always begin
    @(instr);
    #1;
    if(&instr[1:0])
        case(opcode)
        LUI_OPCODE: begin
            opcode_type = "(     LUI      )";
        end
        AUIPC_OPCODE: begin
            opcode_type = "(    AUIPC     )";
        end
        JAL_OPCODE: begin
            opcode_type = "(     JAL      )";
        end
        JALR_OPCODE: begin
            opcode_type = instr[14:12]? "( illegal_JALR )": "(     JALR     )";
        end
        BRANCH_OPCODE: begin
            case(instr[14:12])
              3'b000: opcode_type = "(     BEQ      )";
              3'b001: opcode_type = "(     BNE      )";
              3'b100: opcode_type = "(     BLT      )";
              3'b101: opcode_type = "(     BGE      )";
              3'b110: opcode_type = "(     BLTU     )";
              3'b111: opcode_type = "(     BGEU     )";
              default: opcode_type= "(illegal_BRANCH)";
            endcase
        end
        LOAD_OPCODE: begin
            case(instr[14:12])
              3'b000: opcode_type = "(      LB      )";
              3'b001: opcode_type = "(      LH      )";
              3'b010: opcode_type = "(      LW      )";
              3'b100: opcode_type = "(      LBU     )";
              3'b101: opcode_type = "(      LHU     )";
              default: opcode_type= "( illegal_LOAD )";
            endcase
        end
        STORE_OPCODE: begin
            case(instr[14:12])
              3'b000: opcode_type = "(      SB      )";
              3'b001: opcode_type = "(      SH      )";
              3'b010: opcode_type = "(      SW      )";
              default: opcode_type = "(illegal_STORE)";
            endcase
        end
        OP_IMM_OPCODE: begin
            case({2'b0,instr[14:12]})
              ALU_ADD  : opcode_type = "(     ADDI     )";
              ALU_XOR  : opcode_type = "(     XORI     )";
              ALU_OR   : opcode_type = "(     ORI      )";
              ALU_AND  : opcode_type = "(     ANDI     )";
              ALU_SRL  : opcode_type = {instr[31],instr[29:25]}? "(illegal_OP_IMM)": instr[30]? "(     SRAI     )": "(     SRLI     )";
              ALU_SLL  : opcode_type = instr[31:25]? "(illegal_OP_IMM)": "(     SLLI     )";
              ALU_SLTS : opcode_type = "(     SLTI     )";
              ALU_SLTU : opcode_type = "(    SLTIU     )";
              default   : opcode_type = "(illegal_OP_IMM)";
            endcase
        end
        OP_OPCODE: begin
            if(!instr[29:25])
            case({instr[31:30],instr[14:12]})
              ALU_ADD  : opcode_type = "(      ADD     )";
              ALU_SUB  : opcode_type = "(      SUB     )";
              ALU_XOR  : opcode_type = "(      XOR     )";
              ALU_OR   : opcode_type = "(      OR      )";
              ALU_AND  : opcode_type = "(      AND     )";
              ALU_SRA  : opcode_type = "(      SRA     )";
              ALU_SRL  : opcode_type = "(      SRL     )";
              ALU_SLL  : opcode_type = "(      SLL     )";
              ALU_SLTU : opcode_type = "(      SLTU    )";
              default   : opcode_type = "(  illegal_OP  )";
            endcase
            else opcode_type = "(  illegal_OP  )";
        end
        MISC_MEM_OPCODE: begin
            opcode_type = instr[14:12]? "(illegal_FENCE )": "(     FENCE    )";
        end
        SYSTEM_OPCODE: begin
            opcode_type = {instr[31:21], instr[19:7]}? "(illegal_SYSTEM)": instr[20]? "(    EBREAK    )": "(    ECALL     )";
        end
        default: opcode_type = "(illegal_opcode)";
        endcase
    else opcode_type = "(illegal_opcode)";
  end

endmodule

// Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// Copyright 2022-2023 Advanced Micro Devices, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2023.1 (win64) Build 3865809 Sun May  7 15:05:29 MDT 2023
// Date        : Thu Oct  5 10:40:50 2023
// Host        : HepoH-HomePC running 64-bit major release  (build 9200)
// Command     : write_verilog C:/Users/voult/Desktop/aps_labs/decoder_netist.v
// Design      : decoder_riscv
// Purpose     : This is a Verilog netlist of the current design or from a specific cell of the design. The output is an
//               IEEE 1364-2001 compliant Verilog HDL file that contains netlist information obtained from the input
//               design files.
// Device      : xc7a100tcsg324-1
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* STRUCTURAL_NETLIST = "yes" *)
module decoder_riscv_ref
   (fetched_instr_i,
    a_sel_o,
    b_sel_o,
    alu_op_o,
    csr_op_o,
    csr_we_o,
    mem_req_o,
    mem_we_o,
    mem_size_o,
    gpr_we_o,
    wb_sel_o,
    illegal_instr_o,
    branch_o,
    jal_o,
    jalr_o,
    mret_o);
  input [31:0]fetched_instr_i;
  output [1:0]a_sel_o;
  output [2:0]b_sel_o;
  output [4:0]alu_op_o;
  output [2:0]csr_op_o;
  output csr_we_o;
  output mem_req_o;
  output mem_we_o;
  output [2:0]mem_size_o;
  output gpr_we_o;
  output [1:0]wb_sel_o;
  output illegal_instr_o;
  output branch_o;
  output jal_o;
  output jalr_o;
  output mret_o;

  wire [1:0]a_sel_o;
  wire \a_sel_o[0]_INST_0_i_1_n_0 ;
  wire \a_sel_o[1]_INST_0_i_1_n_0 ;
  wire [4:0]alu_op_o;
  wire \alu_op_o[3]_INST_0_i_1_n_0 ;
  wire [2:0]b_sel_o;
  wire \b_sel_o[0]_INST_0_i_1_n_0 ;
  wire \b_sel_o[1]_INST_0_i_1_n_0 ;
  wire branch_o;
  wire csr_we_o;
  wire csr_we_o_INST_0_i_1_n_0;
  wire [31:0]fetched_instr_i;
  wire gpr_we_o;
  wire gpr_we_o_INST_0_i_1_n_0;
  wire gpr_we_o_INST_0_i_2_n_0;
  wire gpr_we_o_INST_0_i_3_n_0;
  wire gpr_we_o_INST_0_i_4_n_0;
  wire gpr_we_o_INST_0_i_5_n_0;
  wire gpr_we_o_INST_0_i_6_n_0;
  wire gpr_we_o_INST_0_i_7_n_0;
  wire gpr_we_o_INST_0_i_8_n_0;
  wire illegal_instr_o;
  wire illegal_instr_o_INST_0_i_10_n_0;
  wire illegal_instr_o_INST_0_i_11_n_0;
  wire illegal_instr_o_INST_0_i_12_n_0;
  wire illegal_instr_o_INST_0_i_13_n_0;
  wire illegal_instr_o_INST_0_i_14_n_0;
  wire illegal_instr_o_INST_0_i_15_n_0;
  wire illegal_instr_o_INST_0_i_16_n_0;
  wire illegal_instr_o_INST_0_i_17_n_0;
  wire illegal_instr_o_INST_0_i_1_n_0;
  wire illegal_instr_o_INST_0_i_2_n_0;
  wire illegal_instr_o_INST_0_i_3_n_0;
  wire illegal_instr_o_INST_0_i_4_n_0;
  wire illegal_instr_o_INST_0_i_5_n_0;
  wire illegal_instr_o_INST_0_i_6_n_0;
  wire illegal_instr_o_INST_0_i_7_n_0;
  wire illegal_instr_o_INST_0_i_8_n_0;
  wire illegal_instr_o_INST_0_i_9_n_0;
  wire jal_o;
  wire jalr_o;
  wire mem_req_o;
  wire mem_req_o_INST_0_i_1_n_0;
  wire [2:0]mem_size_o;
  wire mem_we_o;
  wire mret_o;
  wire mret_o_INST_0_i_1_n_0;
  wire [1:0]wb_sel_o;

  assign csr_op_o[2:0] = fetched_instr_i[14:12];
  LUT6 #(
    .INIT(64'h0001000030000000)) 
    \a_sel_o[0]_INST_0 
       (.I0(fetched_instr_i[3]),
        .I1(\a_sel_o[0]_INST_0_i_1_n_0 ),
        .I2(fetched_instr_i[6]),
        .I3(fetched_instr_i[5]),
        .I4(fetched_instr_i[2]),
        .I5(fetched_instr_i[4]),
        .O(a_sel_o[0]));
  LUT2 #(
    .INIT(4'h7)) 
    \a_sel_o[0]_INST_0_i_1 
       (.I0(fetched_instr_i[0]),
        .I1(fetched_instr_i[1]),
        .O(\a_sel_o[0]_INST_0_i_1_n_0 ));
  LUT2 #(
    .INIT(4'h8)) 
    \a_sel_o[1]_INST_0 
       (.I0(\a_sel_o[1]_INST_0_i_1_n_0 ),
        .I1(fetched_instr_i[5]),
        .O(a_sel_o[1]));
  LUT6 #(
    .INIT(64'h0000080000000000)) 
    \a_sel_o[1]_INST_0_i_1 
       (.I0(fetched_instr_i[1]),
        .I1(fetched_instr_i[0]),
        .I2(fetched_instr_i[3]),
        .I3(fetched_instr_i[4]),
        .I4(fetched_instr_i[6]),
        .I5(fetched_instr_i[2]),
        .O(\a_sel_o[1]_INST_0_i_1_n_0 ));
  LUT5 #(
    .INIT(32'h60400000)) 
    \alu_op_o[0]_INST_0 
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[4]),
        .I2(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I3(fetched_instr_i[5]),
        .I4(fetched_instr_i[12]),
        .O(alu_op_o[0]));
  LUT5 #(
    .INIT(32'h60400000)) 
    \alu_op_o[1]_INST_0 
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[4]),
        .I2(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I3(fetched_instr_i[5]),
        .I4(fetched_instr_i[13]),
        .O(alu_op_o[1]));
  LUT5 #(
    .INIT(32'h60400000)) 
    \alu_op_o[2]_INST_0 
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[4]),
        .I2(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I3(fetched_instr_i[5]),
        .I4(fetched_instr_i[14]),
        .O(alu_op_o[2]));
  LUT6 #(
    .INIT(64'h0000C400F0000000)) 
    \alu_op_o[3]_INST_0 
       (.I0(\alu_op_o[3]_INST_0_i_1_n_0 ),
        .I1(fetched_instr_i[30]),
        .I2(fetched_instr_i[5]),
        .I3(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I4(fetched_instr_i[6]),
        .I5(fetched_instr_i[4]),
        .O(alu_op_o[3]));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT2 #(
    .INIT(4'hB)) 
    \alu_op_o[3]_INST_0_i_1 
       (.I0(fetched_instr_i[13]),
        .I1(fetched_instr_i[12]),
        .O(\alu_op_o[3]_INST_0_i_1_n_0 ));
  LUT4 #(
    .INIT(16'h0800)) 
    \alu_op_o[4]_INST_0 
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[5]),
        .I2(fetched_instr_i[4]),
        .I3(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .O(alu_op_o[4]));
  LUT4 #(
    .INIT(16'h1030)) 
    \b_sel_o[0]_INST_0 
       (.I0(fetched_instr_i[5]),
        .I1(fetched_instr_i[6]),
        .I2(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I3(fetched_instr_i[4]),
        .O(b_sel_o[0]));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT4 #(
    .INIT(16'h0040)) 
    \b_sel_o[0]_INST_0_i_1 
       (.I0(fetched_instr_i[3]),
        .I1(fetched_instr_i[0]),
        .I2(fetched_instr_i[1]),
        .I3(fetched_instr_i[2]),
        .O(\b_sel_o[0]_INST_0_i_1_n_0 ));
  LUT5 #(
    .INIT(32'h0C020000)) 
    \b_sel_o[1]_INST_0 
       (.I0(fetched_instr_i[5]),
        .I1(fetched_instr_i[2]),
        .I2(fetched_instr_i[6]),
        .I3(fetched_instr_i[4]),
        .I4(\b_sel_o[1]_INST_0_i_1_n_0 ),
        .O(b_sel_o[1]));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT3 #(
    .INIT(8'h08)) 
    \b_sel_o[1]_INST_0_i_1 
       (.I0(fetched_instr_i[1]),
        .I1(fetched_instr_i[0]),
        .I2(fetched_instr_i[3]),
        .O(\b_sel_o[1]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h4000000000000000)) 
    \b_sel_o[2]_INST_0 
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[2]),
        .I2(fetched_instr_i[5]),
        .I3(fetched_instr_i[6]),
        .I4(fetched_instr_i[1]),
        .I5(fetched_instr_i[0]),
        .O(b_sel_o[2]));
  LUT6 #(
    .INIT(64'h0000808800000000)) 
    branch_o_INST_0
       (.I0(fetched_instr_i[5]),
        .I1(fetched_instr_i[6]),
        .I2(fetched_instr_i[14]),
        .I3(fetched_instr_i[13]),
        .I4(fetched_instr_i[4]),
        .I5(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .O(branch_o));
  LUT5 #(
    .INIT(32'h80000000)) 
    csr_we_o_INST_0
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[6]),
        .I2(csr_we_o_INST_0_i_1_n_0),
        .I3(fetched_instr_i[5]),
        .I4(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .O(csr_we_o));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT3 #(
    .INIT(8'hFE)) 
    csr_we_o_INST_0_i_1
       (.I0(fetched_instr_i[14]),
        .I1(fetched_instr_i[12]),
        .I2(fetched_instr_i[13]),
        .O(csr_we_o_INST_0_i_1_n_0));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFF020)) 
    gpr_we_o_INST_0
       (.I0(\alu_op_o[3]_INST_0_i_1_n_0 ),
        .I1(fetched_instr_i[5]),
        .I2(gpr_we_o_INST_0_i_1_n_0),
        .I3(gpr_we_o_INST_0_i_2_n_0),
        .I4(gpr_we_o_INST_0_i_3_n_0),
        .I5(gpr_we_o_INST_0_i_4_n_0),
        .O(gpr_we_o));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT5 #(
    .INIT(32'h04000000)) 
    gpr_we_o_INST_0_i_1
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[4]),
        .I2(fetched_instr_i[3]),
        .I3(fetched_instr_i[0]),
        .I4(fetched_instr_i[1]),
        .O(gpr_we_o_INST_0_i_1_n_0));
  LUT6 #(
    .INIT(64'h0082AAAAAAAAAAAA)) 
    gpr_we_o_INST_0_i_2
       (.I0(gpr_we_o_INST_0_i_5_n_0),
        .I1(fetched_instr_i[14]),
        .I2(fetched_instr_i[12]),
        .I3(fetched_instr_i[13]),
        .I4(fetched_instr_i[30]),
        .I5(fetched_instr_i[5]),
        .O(gpr_we_o_INST_0_i_2_n_0));
  LUT6 #(
    .INIT(64'h00000010000000F0)) 
    gpr_we_o_INST_0_i_3
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[13]),
        .I2(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I3(fetched_instr_i[6]),
        .I4(fetched_instr_i[5]),
        .I5(gpr_we_o_INST_0_i_6_n_0),
        .O(gpr_we_o_INST_0_i_3_n_0));
  LUT6 #(
    .INIT(64'hFFF8FF88FFFFFF00)) 
    gpr_we_o_INST_0_i_4
       (.I0(gpr_we_o_INST_0_i_7_n_0),
        .I1(gpr_we_o_INST_0_i_8_n_0),
        .I2(fetched_instr_i[3]),
        .I3(\a_sel_o[1]_INST_0_i_1_n_0 ),
        .I4(b_sel_o[2]),
        .I5(csr_we_o_INST_0_i_1_n_0),
        .O(gpr_we_o_INST_0_i_4_n_0));
  LUT6 #(
    .INIT(64'h0000000000000001)) 
    gpr_we_o_INST_0_i_5
       (.I0(fetched_instr_i[27]),
        .I1(fetched_instr_i[31]),
        .I2(fetched_instr_i[25]),
        .I3(fetched_instr_i[26]),
        .I4(fetched_instr_i[29]),
        .I5(fetched_instr_i[28]),
        .O(gpr_we_o_INST_0_i_5_n_0));
  LUT2 #(
    .INIT(4'hE)) 
    gpr_we_o_INST_0_i_6
       (.I0(fetched_instr_i[12]),
        .I1(fetched_instr_i[14]),
        .O(gpr_we_o_INST_0_i_6_n_0));
  LUT2 #(
    .INIT(4'h8)) 
    gpr_we_o_INST_0_i_7
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[6]),
        .O(gpr_we_o_INST_0_i_7_n_0));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT5 #(
    .INIT(32'h00400000)) 
    gpr_we_o_INST_0_i_8
       (.I0(fetched_instr_i[2]),
        .I1(fetched_instr_i[1]),
        .I2(fetched_instr_i[0]),
        .I3(fetched_instr_i[3]),
        .I4(fetched_instr_i[5]),
        .O(gpr_we_o_INST_0_i_8_n_0));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFEFEFE)) 
    illegal_instr_o_INST_0
       (.I0(illegal_instr_o_INST_0_i_1_n_0),
        .I1(illegal_instr_o_INST_0_i_2_n_0),
        .I2(illegal_instr_o_INST_0_i_3_n_0),
        .I3(illegal_instr_o_INST_0_i_4_n_0),
        .I4(illegal_instr_o_INST_0_i_5_n_0),
        .I5(illegal_instr_o_INST_0_i_6_n_0),
        .O(illegal_instr_o));
  LUT6 #(
    .INIT(64'hF3BBF3BBFF0FFC0F)) 
    illegal_instr_o_INST_0_i_1
       (.I0(illegal_instr_o_INST_0_i_7_n_0),
        .I1(fetched_instr_i[5]),
        .I2(illegal_instr_o_INST_0_i_8_n_0),
        .I3(fetched_instr_i[3]),
        .I4(csr_we_o_INST_0_i_1_n_0),
        .I5(fetched_instr_i[6]),
        .O(illegal_instr_o_INST_0_i_1_n_0));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT4 #(
    .INIT(16'h4440)) 
    illegal_instr_o_INST_0_i_10
       (.I0(fetched_instr_i[2]),
        .I1(fetched_instr_i[4]),
        .I2(fetched_instr_i[29]),
        .I3(fetched_instr_i[28]),
        .O(illegal_instr_o_INST_0_i_10_n_0));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT4 #(
    .INIT(16'h0F44)) 
    illegal_instr_o_INST_0_i_11
       (.I0(fetched_instr_i[13]),
        .I1(fetched_instr_i[12]),
        .I2(fetched_instr_i[6]),
        .I3(fetched_instr_i[5]),
        .O(illegal_instr_o_INST_0_i_11_n_0));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT3 #(
    .INIT(8'h08)) 
    illegal_instr_o_INST_0_i_12
       (.I0(fetched_instr_i[30]),
        .I1(fetched_instr_i[5]),
        .I2(fetched_instr_i[2]),
        .O(illegal_instr_o_INST_0_i_12_n_0));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT5 #(
    .INIT(32'h22320230)) 
    illegal_instr_o_INST_0_i_13
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[6]),
        .I2(fetched_instr_i[14]),
        .I3(fetched_instr_i[12]),
        .I4(fetched_instr_i[13]),
        .O(illegal_instr_o_INST_0_i_13_n_0));
  LUT4 #(
    .INIT(16'hFFFE)) 
    illegal_instr_o_INST_0_i_14
       (.I0(fetched_instr_i[10]),
        .I1(fetched_instr_i[9]),
        .I2(fetched_instr_i[15]),
        .I3(fetched_instr_i[11]),
        .O(illegal_instr_o_INST_0_i_14_n_0));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFBFF)) 
    illegal_instr_o_INST_0_i_15
       (.I0(fetched_instr_i[30]),
        .I1(fetched_instr_i[29]),
        .I2(fetched_instr_i[24]),
        .I3(fetched_instr_i[28]),
        .I4(fetched_instr_i[8]),
        .I5(fetched_instr_i[7]),
        .O(illegal_instr_o_INST_0_i_15_n_0));
  LUT4 #(
    .INIT(16'hFFFD)) 
    illegal_instr_o_INST_0_i_16
       (.I0(fetched_instr_i[21]),
        .I1(fetched_instr_i[20]),
        .I2(fetched_instr_i[23]),
        .I3(fetched_instr_i[22]),
        .O(illegal_instr_o_INST_0_i_16_n_0));
  LUT4 #(
    .INIT(16'hFFFE)) 
    illegal_instr_o_INST_0_i_17
       (.I0(fetched_instr_i[17]),
        .I1(fetched_instr_i[16]),
        .I2(fetched_instr_i[19]),
        .I3(fetched_instr_i[18]),
        .O(illegal_instr_o_INST_0_i_17_n_0));
  LUT6 #(
    .INIT(64'hFFFFFEEEFEEEFEEE)) 
    illegal_instr_o_INST_0_i_2
       (.I0(\a_sel_o[0]_INST_0_i_1_n_0 ),
        .I1(illegal_instr_o_INST_0_i_9_n_0),
        .I2(illegal_instr_o_INST_0_i_10_n_0),
        .I3(illegal_instr_o_INST_0_i_11_n_0),
        .I4(illegal_instr_o_INST_0_i_12_n_0),
        .I5(illegal_instr_o_INST_0_i_13_n_0),
        .O(illegal_instr_o_INST_0_i_2_n_0));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT3 #(
    .INIT(8'h80)) 
    illegal_instr_o_INST_0_i_3
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[4]),
        .I2(fetched_instr_i[2]),
        .O(illegal_instr_o_INST_0_i_3_n_0));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT5 #(
    .INIT(32'h00000008)) 
    illegal_instr_o_INST_0_i_4
       (.I0(fetched_instr_i[6]),
        .I1(fetched_instr_i[4]),
        .I2(fetched_instr_i[13]),
        .I3(fetched_instr_i[12]),
        .I4(fetched_instr_i[14]),
        .O(illegal_instr_o_INST_0_i_4_n_0));
  LUT4 #(
    .INIT(16'hFFFE)) 
    illegal_instr_o_INST_0_i_5
       (.I0(illegal_instr_o_INST_0_i_14_n_0),
        .I1(illegal_instr_o_INST_0_i_15_n_0),
        .I2(illegal_instr_o_INST_0_i_16_n_0),
        .I3(illegal_instr_o_INST_0_i_17_n_0),
        .O(illegal_instr_o_INST_0_i_5_n_0));
  LUT6 #(
    .INIT(64'h0080A0A000800080)) 
    illegal_instr_o_INST_0_i_6
       (.I0(mret_o_INST_0_i_1_n_0),
        .I1(fetched_instr_i[6]),
        .I2(fetched_instr_i[4]),
        .I3(csr_we_o_INST_0_i_1_n_0),
        .I4(fetched_instr_i[2]),
        .I5(illegal_instr_o_INST_0_i_11_n_0),
        .O(illegal_instr_o_INST_0_i_6_n_0));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT5 #(
    .INIT(32'hAA8FAA88)) 
    illegal_instr_o_INST_0_i_7
       (.I0(fetched_instr_i[2]),
        .I1(fetched_instr_i[12]),
        .I2(fetched_instr_i[4]),
        .I3(fetched_instr_i[14]),
        .I4(fetched_instr_i[13]),
        .O(illegal_instr_o_INST_0_i_7_n_0));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT2 #(
    .INIT(4'hB)) 
    illegal_instr_o_INST_0_i_8
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[2]),
        .O(illegal_instr_o_INST_0_i_8_n_0));
  LUT6 #(
    .INIT(64'h000044000000FC88)) 
    illegal_instr_o_INST_0_i_9
       (.I0(fetched_instr_i[5]),
        .I1(fetched_instr_i[14]),
        .I2(fetched_instr_i[12]),
        .I3(fetched_instr_i[13]),
        .I4(fetched_instr_i[4]),
        .I5(fetched_instr_i[6]),
        .O(illegal_instr_o_INST_0_i_9_n_0));
  LUT2 #(
    .INIT(4'h8)) 
    jal_o_INST_0
       (.I0(b_sel_o[2]),
        .I1(fetched_instr_i[3]),
        .O(jal_o));
  LUT6 #(
    .INIT(64'h0400000000000000)) 
    jalr_o_INST_0
       (.I0(csr_we_o_INST_0_i_1_n_0),
        .I1(\b_sel_o[1]_INST_0_i_1_n_0 ),
        .I2(fetched_instr_i[4]),
        .I3(fetched_instr_i[2]),
        .I4(fetched_instr_i[5]),
        .I5(fetched_instr_i[6]),
        .O(jalr_o));
  LUT5 #(
    .INIT(32'h040C04CC)) 
    mem_req_o_INST_0
       (.I0(fetched_instr_i[5]),
        .I1(mem_req_o_INST_0_i_1_n_0),
        .I2(fetched_instr_i[13]),
        .I3(fetched_instr_i[14]),
        .I4(fetched_instr_i[12]),
        .O(mem_req_o));
  LUT6 #(
    .INIT(64'h0000000000001000)) 
    mem_req_o_INST_0_i_1
       (.I0(fetched_instr_i[4]),
        .I1(fetched_instr_i[3]),
        .I2(fetched_instr_i[0]),
        .I3(fetched_instr_i[1]),
        .I4(fetched_instr_i[2]),
        .I5(fetched_instr_i[6]),
        .O(mem_req_o_INST_0_i_1_n_0));
  LUT2 #(
    .INIT(4'h8)) 
    \mem_size_o[0]_INST_0 
       (.I0(mem_req_o_INST_0_i_1_n_0),
        .I1(fetched_instr_i[12]),
        .O(mem_size_o[0]));
  LUT2 #(
    .INIT(4'h8)) 
    \mem_size_o[1]_INST_0 
       (.I0(mem_req_o_INST_0_i_1_n_0),
        .I1(fetched_instr_i[13]),
        .O(mem_size_o[1]));
  LUT2 #(
    .INIT(4'h8)) 
    \mem_size_o[2]_INST_0 
       (.I0(mem_req_o_INST_0_i_1_n_0),
        .I1(fetched_instr_i[14]),
        .O(mem_size_o[2]));
  LUT5 #(
    .INIT(32'h020A0000)) 
    mem_we_o_INST_0
       (.I0(fetched_instr_i[5]),
        .I1(fetched_instr_i[13]),
        .I2(fetched_instr_i[14]),
        .I3(fetched_instr_i[12]),
        .I4(mem_req_o_INST_0_i_1_n_0),
        .O(mem_we_o));
  LUT5 #(
    .INIT(32'h00000080)) 
    mret_o_INST_0
       (.I0(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I1(fetched_instr_i[5]),
        .I2(illegal_instr_o_INST_0_i_4_n_0),
        .I3(mret_o_INST_0_i_1_n_0),
        .I4(illegal_instr_o_INST_0_i_5_n_0),
        .O(mret_o));
  LUT4 #(
    .INIT(16'hFFFE)) 
    mret_o_INST_0_i_1
       (.I0(fetched_instr_i[26]),
        .I1(fetched_instr_i[25]),
        .I2(fetched_instr_i[31]),
        .I3(fetched_instr_i[27]),
        .O(mret_o_INST_0_i_1_n_0));
  LUT2 #(
    .INIT(4'h2)) 
    \wb_sel_o[0]_INST_0 
       (.I0(mem_req_o_INST_0_i_1_n_0),
        .I1(fetched_instr_i[5]),
        .O(wb_sel_o[0]));
  LUT4 #(
    .INIT(16'h8000)) 
    \wb_sel_o[1]_INST_0 
       (.I0(fetched_instr_i[5]),
        .I1(\b_sel_o[0]_INST_0_i_1_n_0 ),
        .I2(fetched_instr_i[6]),
        .I3(fetched_instr_i[4]),
        .O(wb_sel_o[1]));
endmodule
