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
  import alu_opcodes_pkg::*;
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
        csr_op_miss     = (grm.csr_op_o !== csr_op) & !illegal_instr;
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
        csr_op_miss     = (grm.csr_op_o !== csr_op) & !illegal_instr;
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
        csr_op_miss     = (grm.csr_op_o !== csr_op) & !illegal_instr;
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
        csr_op_miss     = (grm.csr_op_o !== csr_op) & !illegal_instr;
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
      
      default:      //MISC_MEM_OPCODE, SYSTEM_OPCODE and other
      begin
        //a_sel_miss      = grm.a_sel_o !== a_sel;
        //b_sel_miss      = grm.b_sel_o !== b_sel;
        //alu_op_miss     = grm.alu_op_o !== alu_op;
        csr_op_miss     = (grm.csr_op_o !== csr_op);
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
      if (csr_we_miss) begin
        $display ("Output 'csr_we_o       ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",csr_we, grm.csr_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
      end
      if (mem_we_miss)begin
        $display ("Output 'mem_we_o       ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",mem_we, grm.mem_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (mem_size_miss)begin
        $display ("Output 'mem_size_o     ' is incorrect( %b  instead of %b  ), instruction: %s %s, time: %t",mem_size, grm.mem_size_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (mem_req_miss)begin
        $display ("Output 'mem_req_o      ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",mem_req, grm.mem_req_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (wb_sel_miss)begin
        $display ("Output 'wb_sel_o   ' is incorrect(   %b  instead of %b    ), instruction: %s %s, time: %t",wb_sel, grm.wb_sel_o, instr_type, opcode_type, $time);
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
    end

    if ((a_sel != OP_A_RS1) &
        (a_sel != OP_A_CURR_PC) &
        (a_sel != OP_A_ZERO)) begin
      $display ("Output 'a_sel_o' must always have a legal value, instruction: %s %s, time: %t", instr_type, opcode_type, $time);
      error = error + 1;
    end
    if ((b_sel != OP_B_RS2) &
        (b_sel != OP_B_IMM_I) &
        (b_sel != OP_B_IMM_U) &
        (b_sel != OP_B_IMM_S) &
        (b_sel != OP_B_INCR)) begin
      $display ("Output 'b_sel_o' must always have a legal value, instruction: %s %s, time: %t", instr_type, opcode_type, $time);
      error = error + 1;
    end
    if ((alu_op != ALU_ADD)  & (alu_op != ALU_SUB) &
        (alu_op != ALU_XOR)  & (alu_op != ALU_OR)  &
        (alu_op != ALU_AND)  & (alu_op != ALU_SRA) &
        (alu_op != ALU_SRL)  & (alu_op != ALU_SLL) &
        (alu_op != ALU_LTS)  & (alu_op != ALU_LTU) &
        (alu_op != ALU_GES)  & (alu_op != ALU_GEU) &
        (alu_op != ALU_EQ)   & (alu_op != ALU_NE)  &
        (alu_op != ALU_SLTS) & (alu_op != ALU_SLTU)) begin
      $display ("Output 'alu_op_o' must always have a legal value, instruction: %s %s, time: %t", instr_type, opcode_type, $time);
      error = error + 1;
    end
    if ((mem_size != LDST_B) &
        (mem_size != LDST_H) &
        (mem_size != LDST_W) &
        (mem_size != LDST_BU) &
        (mem_size != LDST_HU)) begin
      $display ("Output 'mem_size_o' must always have a legal value, instruction: %s %s, time: %t", instr_type, opcode_type, $time);
      error = error + 1;
    end
    if ((wb_sel != WB_EX_RESULT) &
        (wb_sel != WB_LSU_DATA)) begin
      $display ("Output 'wb_sel_o' must always have a legal value, instruction: %s %s, time: %t", instr_type, opcode_type, $time);
      error = error + 1;
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

  wire \<const0> ;
  wire [1:0]a_sel_o;
  wire [1:0]a_sel_o_OBUF;
  wire \a_sel_o_OBUF[0]_inst_i_2_n_0 ;
  wire \a_sel_o_OBUF[0]_inst_i_3_n_0 ;
  wire \a_sel_o_OBUF[1]_inst_i_2_n_0 ;
  wire [4:0]alu_op_o;
  wire [4:0]alu_op_o_OBUF;
  wire \alu_op_o_OBUF[1]_inst_i_2_n_0 ;
  wire \alu_op_o_OBUF[1]_inst_i_3_n_0 ;
  wire \alu_op_o_OBUF[1]_inst_i_4_n_0 ;
  wire \alu_op_o_OBUF[3]_inst_i_2_n_0 ;
  wire \alu_op_o_OBUF[3]_inst_i_3_n_0 ;
  wire \alu_op_o_OBUF[3]_inst_i_4_n_0 ;
  wire \alu_op_o_OBUF[4]_inst_i_2_n_0 ;
  wire [2:0]b_sel_o;
  wire [2:0]b_sel_o_OBUF;
  wire \b_sel_o_OBUF[0]_inst_i_2_n_0 ;
  wire \b_sel_o_OBUF[0]_inst_i_3_n_0 ;
  wire \b_sel_o_OBUF[0]_inst_i_4_n_0 ;
  wire \b_sel_o_OBUF[0]_inst_i_5_n_0 ;
  wire \b_sel_o_OBUF[1]_inst_i_2_n_0 ;
  wire \b_sel_o_OBUF[2]_inst_i_2_n_0 ;
  wire branch_o;
  wire branch_o_OBUF;
  wire [2:0]csr_op_o;
  wire [2:0]csr_op_o_OBUF;
  wire \csr_op_o_OBUF[1]_inst_i_2_n_0 ;
  wire \csr_op_o_OBUF[2]_inst_i_2_n_0 ;
  wire csr_we_o;
  wire csr_we_o_OBUF;
  wire csr_we_o_OBUF_inst_i_2_n_0;
  wire [31:0]fetched_instr_i;
  wire [31:0]fetched_instr_i_IBUF;
  wire gpr_we_o;
  wire gpr_we_o_OBUF;
  wire gpr_we_o_OBUF_inst_i_2_n_0;
  wire illegal_instr_o;
  wire illegal_instr_o_OBUF;
  wire illegal_instr_o_OBUF_inst_i_2_n_0;
  wire illegal_instr_o_OBUF_inst_i_3_n_0;
  wire illegal_instr_o_OBUF_inst_i_4_n_0;
  wire illegal_instr_o_OBUF_inst_i_5_n_0;
  wire illegal_instr_o_OBUF_inst_i_6_n_0;
  wire jal_o;
  wire jal_o_OBUF;
  wire jalr_o;
  wire jalr_o_OBUF;
  wire mem_req_o;
  wire mem_req_o_OBUF;
  wire mem_req_o_OBUF_inst_i_2_n_0;
  wire [2:0]mem_size_o;
  wire [2:0]mem_size_o_OBUF;
  wire mem_we_o;
  wire mem_we_o_OBUF;
  wire mret_o;
  wire mret_o_OBUF;
  wire mret_o_OBUF_inst_i_2_n_0;
  wire mret_o_OBUF_inst_i_3_n_0;
  wire mret_o_OBUF_inst_i_4_n_0;
  wire mret_o_OBUF_inst_i_5_n_0;
  wire mret_o_OBUF_inst_i_6_n_0;
  wire mret_o_OBUF_inst_i_7_n_0;
  wire [1:0]wb_sel_o;
  wire [0:0]wb_sel_o_OBUF;

  GND GND
       (.G(\<const0> ));
  OBUF \a_sel_o_OBUF[0]_inst 
       (.I(a_sel_o_OBUF[0]),
        .O(a_sel_o[0]));
  LUT6 #(
    .INIT(64'h0032000000000300)) 
    \a_sel_o_OBUF[0]_inst_i_1 
       (.I0(\a_sel_o_OBUF[0]_inst_i_2_n_0 ),
        .I1(\a_sel_o_OBUF[0]_inst_i_3_n_0 ),
        .I2(fetched_instr_i_IBUF[3]),
        .I3(fetched_instr_i_IBUF[4]),
        .I4(fetched_instr_i_IBUF[6]),
        .I5(fetched_instr_i_IBUF[5]),
        .O(a_sel_o_OBUF[0]));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT3 #(
    .INIT(8'h01)) 
    \a_sel_o_OBUF[0]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[12]),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[13]),
        .O(\a_sel_o_OBUF[0]_inst_i_2_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair9" *) 
  LUT3 #(
    .INIT(8'h7F)) 
    \a_sel_o_OBUF[0]_inst_i_3 
       (.I0(fetched_instr_i_IBUF[2]),
        .I1(fetched_instr_i_IBUF[1]),
        .I2(fetched_instr_i_IBUF[0]),
        .O(\a_sel_o_OBUF[0]_inst_i_3_n_0 ));
  OBUF \a_sel_o_OBUF[1]_inst 
       (.I(a_sel_o_OBUF[1]),
        .O(a_sel_o[1]));
  LUT6 #(
    .INIT(64'h0008000000000000)) 
    \a_sel_o_OBUF[1]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[5]),
        .I1(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[6]),
        .I3(fetched_instr_i_IBUF[3]),
        .I4(fetched_instr_i_IBUF[2]),
        .I5(fetched_instr_i_IBUF[4]),
        .O(a_sel_o_OBUF[1]));
  LUT2 #(
    .INIT(4'h8)) 
    \a_sel_o_OBUF[1]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[0]),
        .I1(fetched_instr_i_IBUF[1]),
        .O(\a_sel_o_OBUF[1]_inst_i_2_n_0 ));
  OBUF \alu_op_o_OBUF[0]_inst 
       (.I(alu_op_o_OBUF[0]),
        .O(alu_op_o[0]));
  LUT6 #(
    .INIT(64'hA0B0A00000000000)) 
    \alu_op_o_OBUF[0]_inst_i_1 
       (.I0(\alu_op_o_OBUF[1]_inst_i_3_n_0 ),
        .I1(\alu_op_o_OBUF[3]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[12]),
        .I3(fetched_instr_i_IBUF[6]),
        .I4(fetched_instr_i_IBUF[4]),
        .I5(\alu_op_o_OBUF[4]_inst_i_2_n_0 ),
        .O(alu_op_o_OBUF[0]));
  OBUF \alu_op_o_OBUF[1]_inst 
       (.I(alu_op_o_OBUF[1]),
        .O(alu_op_o[1]));
  LUT6 #(
    .INIT(64'h00000000FF450000)) 
    \alu_op_o_OBUF[1]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[6]),
        .I1(\alu_op_o_OBUF[1]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[5]),
        .I3(\alu_op_o_OBUF[1]_inst_i_3_n_0 ),
        .I4(fetched_instr_i_IBUF[13]),
        .I5(\alu_op_o_OBUF[1]_inst_i_4_n_0 ),
        .O(alu_op_o_OBUF[1]));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT5 #(
    .INIT(32'h2222A22A)) 
    \alu_op_o_OBUF[1]_inst_i_2 
       (.I0(\b_sel_o_OBUF[0]_inst_i_5_n_0 ),
        .I1(fetched_instr_i_IBUF[30]),
        .I2(fetched_instr_i_IBUF[12]),
        .I3(fetched_instr_i_IBUF[14]),
        .I4(fetched_instr_i_IBUF[13]),
        .O(\alu_op_o_OBUF[1]_inst_i_2_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT4 #(
    .INIT(16'h4500)) 
    \alu_op_o_OBUF[1]_inst_i_3 
       (.I0(fetched_instr_i_IBUF[4]),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[5]),
        .O(\alu_op_o_OBUF[1]_inst_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hFFF1FFFFFFFFFFFF)) 
    \alu_op_o_OBUF[1]_inst_i_4 
       (.I0(fetched_instr_i_IBUF[6]),
        .I1(fetched_instr_i_IBUF[4]),
        .I2(fetched_instr_i_IBUF[2]),
        .I3(fetched_instr_i_IBUF[3]),
        .I4(fetched_instr_i_IBUF[0]),
        .I5(fetched_instr_i_IBUF[1]),
        .O(\alu_op_o_OBUF[1]_inst_i_4_n_0 ));
  OBUF \alu_op_o_OBUF[2]_inst 
       (.I(alu_op_o_OBUF[2]),
        .O(alu_op_o[2]));
  LUT6 #(
    .INIT(64'h2604000000000000)) 
    \alu_op_o_OBUF[2]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[6]),
        .I1(fetched_instr_i_IBUF[4]),
        .I2(\alu_op_o_OBUF[3]_inst_i_2_n_0 ),
        .I3(fetched_instr_i_IBUF[5]),
        .I4(\alu_op_o_OBUF[4]_inst_i_2_n_0 ),
        .I5(fetched_instr_i_IBUF[14]),
        .O(alu_op_o_OBUF[2]));
  OBUF \alu_op_o_OBUF[3]_inst 
       (.I(alu_op_o_OBUF[3]),
        .O(alu_op_o[3]));
  LUT6 #(
    .INIT(64'h00000020AAAAAAAA)) 
    \alu_op_o_OBUF[3]_inst_i_1 
       (.I0(\alu_op_o_OBUF[4]_inst_i_2_n_0 ),
        .I1(\alu_op_o_OBUF[3]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[4]),
        .I3(fetched_instr_i_IBUF[6]),
        .I4(\alu_op_o_OBUF[3]_inst_i_3_n_0 ),
        .I5(\alu_op_o_OBUF[3]_inst_i_4_n_0 ),
        .O(alu_op_o_OBUF[3]));
  LUT6 #(
    .INIT(64'hA2A2A2A233A2F322)) 
    \alu_op_o_OBUF[3]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[5]),
        .I1(\b_sel_o_OBUF[0]_inst_i_5_n_0 ),
        .I2(fetched_instr_i_IBUF[30]),
        .I3(fetched_instr_i_IBUF[12]),
        .I4(fetched_instr_i_IBUF[14]),
        .I5(fetched_instr_i_IBUF[13]),
        .O(\alu_op_o_OBUF[3]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAEAFAFAFFFFFFFFF)) 
    \alu_op_o_OBUF[3]_inst_i_3 
       (.I0(fetched_instr_i_IBUF[13]),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[12]),
        .I3(\b_sel_o_OBUF[0]_inst_i_5_n_0 ),
        .I4(fetched_instr_i_IBUF[5]),
        .I5(fetched_instr_i_IBUF[30]),
        .O(\alu_op_o_OBUF[3]_inst_i_3_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT5 #(
    .INIT(32'hF7F7FFF7)) 
    \alu_op_o_OBUF[3]_inst_i_4 
       (.I0(fetched_instr_i_IBUF[6]),
        .I1(fetched_instr_i_IBUF[5]),
        .I2(fetched_instr_i_IBUF[4]),
        .I3(fetched_instr_i_IBUF[13]),
        .I4(fetched_instr_i_IBUF[14]),
        .O(\alu_op_o_OBUF[3]_inst_i_4_n_0 ));
  OBUF \alu_op_o_OBUF[4]_inst 
       (.I(alu_op_o_OBUF[4]),
        .O(alu_op_o[4]));
  LUT6 #(
    .INIT(64'h008A000000000000)) 
    \alu_op_o_OBUF[4]_inst_i_1 
       (.I0(\alu_op_o_OBUF[4]_inst_i_2_n_0 ),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[4]),
        .I4(fetched_instr_i_IBUF[5]),
        .I5(fetched_instr_i_IBUF[6]),
        .O(alu_op_o_OBUF[4]));
  (* SOFT_HLUTNM = "soft_lutpair8" *) 
  LUT4 #(
    .INIT(16'h0008)) 
    \alu_op_o_OBUF[4]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[1]),
        .I1(fetched_instr_i_IBUF[0]),
        .I2(fetched_instr_i_IBUF[3]),
        .I3(fetched_instr_i_IBUF[2]),
        .O(\alu_op_o_OBUF[4]_inst_i_2_n_0 ));
  OBUF \b_sel_o_OBUF[0]_inst 
       (.I(b_sel_o_OBUF[0]),
        .O(b_sel_o[0]));
  LUT5 #(
    .INIT(32'h0000E200)) 
    \b_sel_o_OBUF[0]_inst_i_1 
       (.I0(\b_sel_o_OBUF[0]_inst_i_2_n_0 ),
        .I1(fetched_instr_i_IBUF[4]),
        .I2(\b_sel_o_OBUF[0]_inst_i_3_n_0 ),
        .I3(\b_sel_o_OBUF[0]_inst_i_4_n_0 ),
        .I4(fetched_instr_i_IBUF[2]),
        .O(b_sel_o_OBUF[0]));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT4 #(
    .INIT(16'h0377)) 
    \b_sel_o_OBUF[0]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[12]),
        .I1(fetched_instr_i_IBUF[13]),
        .I2(fetched_instr_i_IBUF[5]),
        .I3(fetched_instr_i_IBUF[14]),
        .O(\b_sel_o_OBUF[0]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000000FFFFA2FF)) 
    \b_sel_o_OBUF[0]_inst_i_3 
       (.I0(\b_sel_o_OBUF[0]_inst_i_5_n_0 ),
        .I1(fetched_instr_i_IBUF[30]),
        .I2(fetched_instr_i_IBUF[14]),
        .I3(fetched_instr_i_IBUF[12]),
        .I4(fetched_instr_i_IBUF[13]),
        .I5(fetched_instr_i_IBUF[5]),
        .O(\b_sel_o_OBUF[0]_inst_i_3_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair8" *) 
  LUT4 #(
    .INIT(16'h0008)) 
    \b_sel_o_OBUF[0]_inst_i_4 
       (.I0(fetched_instr_i_IBUF[1]),
        .I1(fetched_instr_i_IBUF[0]),
        .I2(fetched_instr_i_IBUF[6]),
        .I3(fetched_instr_i_IBUF[3]),
        .O(\b_sel_o_OBUF[0]_inst_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000001)) 
    \b_sel_o_OBUF[0]_inst_i_5 
       (.I0(fetched_instr_i_IBUF[26]),
        .I1(fetched_instr_i_IBUF[25]),
        .I2(fetched_instr_i_IBUF[27]),
        .I3(fetched_instr_i_IBUF[28]),
        .I4(fetched_instr_i_IBUF[29]),
        .I5(fetched_instr_i_IBUF[31]),
        .O(\b_sel_o_OBUF[0]_inst_i_5_n_0 ));
  OBUF \b_sel_o_OBUF[1]_inst 
       (.I(b_sel_o_OBUF[1]),
        .O(b_sel_o[1]));
  LUT6 #(
    .INIT(64'h000C000000000004)) 
    \b_sel_o_OBUF[1]_inst_i_1 
       (.I0(\b_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .I1(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[6]),
        .I3(fetched_instr_i_IBUF[3]),
        .I4(fetched_instr_i_IBUF[2]),
        .I5(fetched_instr_i_IBUF[4]),
        .O(b_sel_o_OBUF[1]));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT4 #(
    .INIT(16'hFDDD)) 
    \b_sel_o_OBUF[1]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[5]),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[12]),
        .O(\b_sel_o_OBUF[1]_inst_i_2_n_0 ));
  OBUF \b_sel_o_OBUF[2]_inst 
       (.I(b_sel_o_OBUF[2]),
        .O(b_sel_o[2]));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT5 #(
    .INIT(32'h0000FF01)) 
    \b_sel_o_OBUF[2]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[12]),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[3]),
        .I4(\b_sel_o_OBUF[2]_inst_i_2_n_0 ),
        .O(b_sel_o_OBUF[2]));
  LUT6 #(
    .INIT(64'hFFFFFFFF7FFFFFFF)) 
    \b_sel_o_OBUF[2]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[0]),
        .I1(fetched_instr_i_IBUF[1]),
        .I2(fetched_instr_i_IBUF[2]),
        .I3(fetched_instr_i_IBUF[6]),
        .I4(fetched_instr_i_IBUF[5]),
        .I5(fetched_instr_i_IBUF[4]),
        .O(\b_sel_o_OBUF[2]_inst_i_2_n_0 ));
  OBUF branch_o_OBUF_inst
       (.I(branch_o_OBUF),
        .O(branch_o));
  LUT6 #(
    .INIT(64'h0000000000008000)) 
    branch_o_OBUF_inst_i_1
       (.I0(\alu_op_o_OBUF[1]_inst_i_3_n_0 ),
        .I1(fetched_instr_i_IBUF[6]),
        .I2(fetched_instr_i_IBUF[1]),
        .I3(fetched_instr_i_IBUF[0]),
        .I4(fetched_instr_i_IBUF[2]),
        .I5(fetched_instr_i_IBUF[3]),
        .O(branch_o_OBUF));
  OBUF \csr_op_o_OBUF[0]_inst 
       (.I(csr_op_o_OBUF[0]),
        .O(csr_op_o[0]));
  LUT6 #(
    .INIT(64'h0080000000000000)) 
    \csr_op_o_OBUF[0]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[12]),
        .I1(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[5]),
        .I3(\csr_op_o_OBUF[1]_inst_i_2_n_0 ),
        .I4(fetched_instr_i_IBUF[6]),
        .I5(fetched_instr_i_IBUF[4]),
        .O(csr_op_o_OBUF[0]));
  OBUF \csr_op_o_OBUF[1]_inst 
       (.I(csr_op_o_OBUF[1]),
        .O(csr_op_o[1]));
  LUT6 #(
    .INIT(64'h0080000000000000)) 
    \csr_op_o_OBUF[1]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[13]),
        .I1(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[5]),
        .I3(\csr_op_o_OBUF[1]_inst_i_2_n_0 ),
        .I4(fetched_instr_i_IBUF[6]),
        .I5(fetched_instr_i_IBUF[4]),
        .O(csr_op_o_OBUF[1]));
  (* SOFT_HLUTNM = "soft_lutpair7" *) 
  LUT2 #(
    .INIT(4'hE)) 
    \csr_op_o_OBUF[1]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[2]),
        .I1(fetched_instr_i_IBUF[3]),
        .O(\csr_op_o_OBUF[1]_inst_i_2_n_0 ));
  OBUF \csr_op_o_OBUF[2]_inst 
       (.I(csr_op_o_OBUF[2]),
        .O(csr_op_o[2]));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT4 #(
    .INIT(16'h0A08)) 
    \csr_op_o_OBUF[2]_inst_i_1 
       (.I0(fetched_instr_i_IBUF[14]),
        .I1(fetched_instr_i_IBUF[12]),
        .I2(\csr_op_o_OBUF[2]_inst_i_2_n_0 ),
        .I3(fetched_instr_i_IBUF[13]),
        .O(csr_op_o_OBUF[2]));
  LUT6 #(
    .INIT(64'hFFF7FFFFFFFFFFFF)) 
    \csr_op_o_OBUF[2]_inst_i_2 
       (.I0(fetched_instr_i_IBUF[4]),
        .I1(fetched_instr_i_IBUF[6]),
        .I2(fetched_instr_i_IBUF[2]),
        .I3(fetched_instr_i_IBUF[3]),
        .I4(fetched_instr_i_IBUF[5]),
        .I5(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .O(\csr_op_o_OBUF[2]_inst_i_2_n_0 ));
  OBUF csr_we_o_OBUF_inst
       (.I(csr_we_o_OBUF),
        .O(csr_we_o));
  LUT6 #(
    .INIT(64'h0000C00000008000)) 
    csr_we_o_OBUF_inst_i_1
       (.I0(fetched_instr_i_IBUF[12]),
        .I1(fetched_instr_i_IBUF[1]),
        .I2(fetched_instr_i_IBUF[0]),
        .I3(fetched_instr_i_IBUF[5]),
        .I4(csr_we_o_OBUF_inst_i_2_n_0),
        .I5(fetched_instr_i_IBUF[13]),
        .O(csr_we_o_OBUF));
  (* SOFT_HLUTNM = "soft_lutpair7" *) 
  LUT4 #(
    .INIT(16'hEFFF)) 
    csr_we_o_OBUF_inst_i_2
       (.I0(fetched_instr_i_IBUF[3]),
        .I1(fetched_instr_i_IBUF[2]),
        .I2(fetched_instr_i_IBUF[6]),
        .I3(fetched_instr_i_IBUF[4]),
        .O(csr_we_o_OBUF_inst_i_2_n_0));
  IBUF \fetched_instr_i_IBUF[0]_inst 
       (.I(fetched_instr_i[0]),
        .O(fetched_instr_i_IBUF[0]));
  IBUF \fetched_instr_i_IBUF[10]_inst 
       (.I(fetched_instr_i[10]),
        .O(fetched_instr_i_IBUF[10]));
  IBUF \fetched_instr_i_IBUF[11]_inst 
       (.I(fetched_instr_i[11]),
        .O(fetched_instr_i_IBUF[11]));
  IBUF \fetched_instr_i_IBUF[12]_inst 
       (.I(fetched_instr_i[12]),
        .O(fetched_instr_i_IBUF[12]));
  IBUF \fetched_instr_i_IBUF[13]_inst 
       (.I(fetched_instr_i[13]),
        .O(fetched_instr_i_IBUF[13]));
  IBUF \fetched_instr_i_IBUF[14]_inst 
       (.I(fetched_instr_i[14]),
        .O(fetched_instr_i_IBUF[14]));
  IBUF \fetched_instr_i_IBUF[15]_inst 
       (.I(fetched_instr_i[15]),
        .O(fetched_instr_i_IBUF[15]));
  IBUF \fetched_instr_i_IBUF[16]_inst 
       (.I(fetched_instr_i[16]),
        .O(fetched_instr_i_IBUF[16]));
  IBUF \fetched_instr_i_IBUF[17]_inst 
       (.I(fetched_instr_i[17]),
        .O(fetched_instr_i_IBUF[17]));
  IBUF \fetched_instr_i_IBUF[18]_inst 
       (.I(fetched_instr_i[18]),
        .O(fetched_instr_i_IBUF[18]));
  IBUF \fetched_instr_i_IBUF[19]_inst 
       (.I(fetched_instr_i[19]),
        .O(fetched_instr_i_IBUF[19]));
  IBUF \fetched_instr_i_IBUF[1]_inst 
       (.I(fetched_instr_i[1]),
        .O(fetched_instr_i_IBUF[1]));
  IBUF \fetched_instr_i_IBUF[20]_inst 
       (.I(fetched_instr_i[20]),
        .O(fetched_instr_i_IBUF[20]));
  IBUF \fetched_instr_i_IBUF[21]_inst 
       (.I(fetched_instr_i[21]),
        .O(fetched_instr_i_IBUF[21]));
  IBUF \fetched_instr_i_IBUF[22]_inst 
       (.I(fetched_instr_i[22]),
        .O(fetched_instr_i_IBUF[22]));
  IBUF \fetched_instr_i_IBUF[23]_inst 
       (.I(fetched_instr_i[23]),
        .O(fetched_instr_i_IBUF[23]));
  IBUF \fetched_instr_i_IBUF[24]_inst 
       (.I(fetched_instr_i[24]),
        .O(fetched_instr_i_IBUF[24]));
  IBUF \fetched_instr_i_IBUF[25]_inst 
       (.I(fetched_instr_i[25]),
        .O(fetched_instr_i_IBUF[25]));
  IBUF \fetched_instr_i_IBUF[26]_inst 
       (.I(fetched_instr_i[26]),
        .O(fetched_instr_i_IBUF[26]));
  IBUF \fetched_instr_i_IBUF[27]_inst 
       (.I(fetched_instr_i[27]),
        .O(fetched_instr_i_IBUF[27]));
  IBUF \fetched_instr_i_IBUF[28]_inst 
       (.I(fetched_instr_i[28]),
        .O(fetched_instr_i_IBUF[28]));
  IBUF \fetched_instr_i_IBUF[29]_inst 
       (.I(fetched_instr_i[29]),
        .O(fetched_instr_i_IBUF[29]));
  IBUF \fetched_instr_i_IBUF[2]_inst 
       (.I(fetched_instr_i[2]),
        .O(fetched_instr_i_IBUF[2]));
  IBUF \fetched_instr_i_IBUF[30]_inst 
       (.I(fetched_instr_i[30]),
        .O(fetched_instr_i_IBUF[30]));
  IBUF \fetched_instr_i_IBUF[31]_inst 
       (.I(fetched_instr_i[31]),
        .O(fetched_instr_i_IBUF[31]));
  IBUF \fetched_instr_i_IBUF[3]_inst 
       (.I(fetched_instr_i[3]),
        .O(fetched_instr_i_IBUF[3]));
  IBUF \fetched_instr_i_IBUF[4]_inst 
       (.I(fetched_instr_i[4]),
        .O(fetched_instr_i_IBUF[4]));
  IBUF \fetched_instr_i_IBUF[5]_inst 
       (.I(fetched_instr_i[5]),
        .O(fetched_instr_i_IBUF[5]));
  IBUF \fetched_instr_i_IBUF[6]_inst 
       (.I(fetched_instr_i[6]),
        .O(fetched_instr_i_IBUF[6]));
  IBUF \fetched_instr_i_IBUF[7]_inst 
       (.I(fetched_instr_i[7]),
        .O(fetched_instr_i_IBUF[7]));
  IBUF \fetched_instr_i_IBUF[8]_inst 
       (.I(fetched_instr_i[8]),
        .O(fetched_instr_i_IBUF[8]));
  IBUF \fetched_instr_i_IBUF[9]_inst 
       (.I(fetched_instr_i[9]),
        .O(fetched_instr_i_IBUF[9]));
  OBUF gpr_we_o_OBUF_inst
       (.I(gpr_we_o_OBUF),
        .O(gpr_we_o));
  LUT6 #(
    .INIT(64'hEAEEEEEEEAEEAAAA)) 
    gpr_we_o_OBUF_inst_i_1
       (.I0(b_sel_o_OBUF[2]),
        .I1(\b_sel_o_OBUF[0]_inst_i_4_n_0 ),
        .I2(fetched_instr_i_IBUF[2]),
        .I3(\alu_op_o_OBUF[3]_inst_i_2_n_0 ),
        .I4(fetched_instr_i_IBUF[4]),
        .I5(gpr_we_o_OBUF_inst_i_2_n_0),
        .O(gpr_we_o_OBUF));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT5 #(
    .INIT(32'h0000001F)) 
    gpr_we_o_OBUF_inst_i_2
       (.I0(fetched_instr_i_IBUF[14]),
        .I1(fetched_instr_i_IBUF[12]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[5]),
        .I4(fetched_instr_i_IBUF[2]),
        .O(gpr_we_o_OBUF_inst_i_2_n_0));
  OBUF illegal_instr_o_OBUF_inst
       (.I(illegal_instr_o_OBUF),
        .O(illegal_instr_o));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFF40)) 
    illegal_instr_o_OBUF_inst_i_1
       (.I0(fetched_instr_i_IBUF[2]),
        .I1(\alu_op_o_OBUF[3]_inst_i_2_n_0 ),
        .I2(illegal_instr_o_OBUF_inst_i_2_n_0),
        .I3(illegal_instr_o_OBUF_inst_i_3_n_0),
        .I4(illegal_instr_o_OBUF_inst_i_4_n_0),
        .I5(illegal_instr_o_OBUF_inst_i_5_n_0),
        .O(illegal_instr_o_OBUF));
  (* SOFT_HLUTNM = "soft_lutpair11" *) 
  LUT2 #(
    .INIT(4'h2)) 
    illegal_instr_o_OBUF_inst_i_2
       (.I0(fetched_instr_i_IBUF[4]),
        .I1(fetched_instr_i_IBUF[6]),
        .O(illegal_instr_o_OBUF_inst_i_2_n_0));
  (* SOFT_HLUTNM = "soft_lutpair9" *) 
  LUT4 #(
    .INIT(16'h2FFF)) 
    illegal_instr_o_OBUF_inst_i_3
       (.I0(fetched_instr_i_IBUF[6]),
        .I1(fetched_instr_i_IBUF[5]),
        .I2(fetched_instr_i_IBUF[0]),
        .I3(fetched_instr_i_IBUF[1]),
        .O(illegal_instr_o_OBUF_inst_i_3_n_0));
  LUT6 #(
    .INIT(64'hABF0ABB0F0F0F0F0)) 
    illegal_instr_o_OBUF_inst_i_4
       (.I0(fetched_instr_i_IBUF[4]),
        .I1(\a_sel_o_OBUF[0]_inst_i_2_n_0 ),
        .I2(fetched_instr_i_IBUF[3]),
        .I3(fetched_instr_i_IBUF[6]),
        .I4(fetched_instr_i_IBUF[5]),
        .I5(fetched_instr_i_IBUF[2]),
        .O(illegal_instr_o_OBUF_inst_i_4_n_0));
  (* SOFT_HLUTNM = "soft_lutpair11" *) 
  LUT3 #(
    .INIT(8'h01)) 
    illegal_instr_o_OBUF_inst_i_5
       (.I0(fetched_instr_i_IBUF[3]),
        .I1(fetched_instr_i_IBUF[4]),
        .I2(illegal_instr_o_OBUF_inst_i_6_n_0),
        .O(illegal_instr_o_OBUF_inst_i_5_n_0));
  LUT6 #(
    .INIT(64'hCCCC89DD00110111)) 
    illegal_instr_o_OBUF_inst_i_6
       (.I0(fetched_instr_i_IBUF[2]),
        .I1(fetched_instr_i_IBUF[6]),
        .I2(fetched_instr_i_IBUF[12]),
        .I3(fetched_instr_i_IBUF[13]),
        .I4(fetched_instr_i_IBUF[14]),
        .I5(fetched_instr_i_IBUF[5]),
        .O(illegal_instr_o_OBUF_inst_i_6_n_0));
  OBUF jal_o_OBUF_inst
       (.I(jal_o_OBUF),
        .O(jal_o));
  LUT6 #(
    .INIT(64'h2000000000000000)) 
    jal_o_OBUF_inst_i_1
       (.I0(fetched_instr_i_IBUF[3]),
        .I1(fetched_instr_i_IBUF[4]),
        .I2(fetched_instr_i_IBUF[5]),
        .I3(fetched_instr_i_IBUF[6]),
        .I4(fetched_instr_i_IBUF[2]),
        .I5(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .O(jal_o_OBUF));
  OBUF jalr_o_OBUF_inst
       (.I(jalr_o_OBUF),
        .O(jalr_o));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT5 #(
    .INIT(32'hFFFFFFFE)) 
    jalr_o_OBUF_inst_i_1
       (.I0(\b_sel_o_OBUF[2]_inst_i_2_n_0 ),
        .I1(fetched_instr_i_IBUF[12]),
        .I2(fetched_instr_i_IBUF[14]),
        .I3(fetched_instr_i_IBUF[13]),
        .I4(fetched_instr_i_IBUF[3]),
        .O(jalr_o_OBUF));
  OBUF mem_req_o_OBUF_inst
       (.I(mem_req_o_OBUF),
        .O(mem_req_o));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT5 #(
    .INIT(32'h07570000)) 
    mem_req_o_OBUF_inst_i_1
       (.I0(fetched_instr_i_IBUF[14]),
        .I1(fetched_instr_i_IBUF[5]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[12]),
        .I4(mem_req_o_OBUF_inst_i_2_n_0),
        .O(mem_req_o_OBUF));
  LUT6 #(
    .INIT(64'h0000000000001000)) 
    mem_req_o_OBUF_inst_i_2
       (.I0(fetched_instr_i_IBUF[2]),
        .I1(fetched_instr_i_IBUF[3]),
        .I2(fetched_instr_i_IBUF[0]),
        .I3(fetched_instr_i_IBUF[1]),
        .I4(fetched_instr_i_IBUF[6]),
        .I5(fetched_instr_i_IBUF[4]),
        .O(mem_req_o_OBUF_inst_i_2_n_0));
  OBUF \mem_size_o_OBUF[0]_inst 
       (.I(mem_size_o_OBUF[0]),
        .O(mem_size_o[0]));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT5 #(
    .INIT(32'h002A0000)) 
    \mem_size_o_OBUF[0]_inst_i_1 
       (.I0(mem_req_o_OBUF_inst_i_2_n_0),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[5]),
        .I3(fetched_instr_i_IBUF[13]),
        .I4(fetched_instr_i_IBUF[12]),
        .O(mem_size_o_OBUF[0]));
  OBUF \mem_size_o_OBUF[1]_inst 
       (.I(mem_size_o_OBUF[1]),
        .O(mem_size_o[1]));
  (* SOFT_HLUTNM = "soft_lutpair10" *) 
  LUT4 #(
    .INIT(16'h0020)) 
    \mem_size_o_OBUF[1]_inst_i_1 
       (.I0(mem_req_o_OBUF_inst_i_2_n_0),
        .I1(fetched_instr_i_IBUF[12]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[14]),
        .O(mem_size_o_OBUF[1]));
  OBUF \mem_size_o_OBUF[2]_inst 
       (.I(mem_size_o_OBUF[2]),
        .O(mem_size_o[2]));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT4 #(
    .INIT(16'h0008)) 
    \mem_size_o_OBUF[2]_inst_i_1 
       (.I0(mem_req_o_OBUF_inst_i_2_n_0),
        .I1(fetched_instr_i_IBUF[14]),
        .I2(fetched_instr_i_IBUF[13]),
        .I3(fetched_instr_i_IBUF[5]),
        .O(mem_size_o_OBUF[2]));
  OBUF mem_we_o_OBUF_inst
       (.I(mem_we_o_OBUF),
        .O(mem_we_o));
  LUT6 #(
    .INIT(64'h0000000100000000)) 
    mem_we_o_OBUF_inst_i_1
       (.I0(fetched_instr_i_IBUF[2]),
        .I1(fetched_instr_i_IBUF[4]),
        .I2(\b_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .I3(fetched_instr_i_IBUF[3]),
        .I4(fetched_instr_i_IBUF[6]),
        .I5(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .O(mem_we_o_OBUF));
  OBUF mret_o_OBUF_inst
       (.I(mret_o_OBUF),
        .O(mret_o));
  LUT6 #(
    .INIT(64'h0000000002000000)) 
    mret_o_OBUF_inst_i_1
       (.I0(mret_o_OBUF_inst_i_2_n_0),
        .I1(mret_o_OBUF_inst_i_3_n_0),
        .I2(csr_we_o_OBUF_inst_i_2_n_0),
        .I3(fetched_instr_i_IBUF[5]),
        .I4(mret_o_OBUF_inst_i_4_n_0),
        .I5(mret_o_OBUF_inst_i_5_n_0),
        .O(mret_o_OBUF));
  LUT6 #(
    .INIT(64'h0000000000000020)) 
    mret_o_OBUF_inst_i_2
       (.I0(mret_o_OBUF_inst_i_6_n_0),
        .I1(mret_o_OBUF_inst_i_7_n_0),
        .I2(fetched_instr_i_IBUF[29]),
        .I3(fetched_instr_i_IBUF[16]),
        .I4(fetched_instr_i_IBUF[7]),
        .I5(fetched_instr_i_IBUF[8]),
        .O(mret_o_OBUF_inst_i_2_n_0));
  LUT6 #(
    .INIT(64'hFFFFFFFEFFFFFFFF)) 
    mret_o_OBUF_inst_i_3
       (.I0(fetched_instr_i_IBUF[26]),
        .I1(fetched_instr_i_IBUF[25]),
        .I2(fetched_instr_i_IBUF[27]),
        .I3(fetched_instr_i_IBUF[14]),
        .I4(fetched_instr_i_IBUF[12]),
        .I5(\a_sel_o_OBUF[1]_inst_i_2_n_0 ),
        .O(mret_o_OBUF_inst_i_3_n_0));
  (* SOFT_HLUTNM = "soft_lutpair10" *) 
  LUT2 #(
    .INIT(4'hB)) 
    mret_o_OBUF_inst_i_4
       (.I0(fetched_instr_i_IBUF[14]),
        .I1(fetched_instr_i_IBUF[13]),
        .O(mret_o_OBUF_inst_i_4_n_0));
  LUT5 #(
    .INIT(32'hFFFFFFFD)) 
    mret_o_OBUF_inst_i_5
       (.I0(fetched_instr_i_IBUF[21]),
        .I1(fetched_instr_i_IBUF[31]),
        .I2(fetched_instr_i_IBUF[24]),
        .I3(fetched_instr_i_IBUF[23]),
        .I4(fetched_instr_i_IBUF[15]),
        .O(mret_o_OBUF_inst_i_5_n_0));
  LUT6 #(
    .INIT(64'h0000000000000004)) 
    mret_o_OBUF_inst_i_6
       (.I0(fetched_instr_i_IBUF[19]),
        .I1(fetched_instr_i_IBUF[28]),
        .I2(fetched_instr_i_IBUF[9]),
        .I3(fetched_instr_i_IBUF[17]),
        .I4(fetched_instr_i_IBUF[30]),
        .I5(fetched_instr_i_IBUF[10]),
        .O(mret_o_OBUF_inst_i_6_n_0));
  LUT4 #(
    .INIT(16'hFFFE)) 
    mret_o_OBUF_inst_i_7
       (.I0(fetched_instr_i_IBUF[20]),
        .I1(fetched_instr_i_IBUF[18]),
        .I2(fetched_instr_i_IBUF[22]),
        .I3(fetched_instr_i_IBUF[11]),
        .O(mret_o_OBUF_inst_i_7_n_0));
  OBUF \wb_sel_o_OBUF[0]_inst 
       (.I(wb_sel_o_OBUF),
        .O(wb_sel_o[0]));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT5 #(
    .INIT(32'h0000222A)) 
    \wb_sel_o_OBUF[0]_inst_i_1 
       (.I0(mem_req_o_OBUF_inst_i_2_n_0),
        .I1(fetched_instr_i_IBUF[13]),
        .I2(fetched_instr_i_IBUF[12]),
        .I3(fetched_instr_i_IBUF[14]),
        .I4(fetched_instr_i_IBUF[5]),
        .O(wb_sel_o_OBUF));
  OBUF \wb_sel_o_OBUF[1]_inst 
       (.I(\<const0> ),
        .O(wb_sel_o[1]));
endmodule
