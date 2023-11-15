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
    illegal_miss    = grm.illegal_instr_o !== illegal_instr;
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
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end
      
      SYSTEM_OPCODE:  begin
        //a_sel_miss      = (grm.a_sel_o !== a_sel) & !illegal_instr;
        //b_sel_miss      = (grm.b_sel_o !== b_sel) & !illegal_instr;
        //alu_op_miss     = ((alu_op !== ALU_ADD)&(alu_op !== ALU_XOR)&(alu_op !== ALU_OR)) & !illegal_instr;
        csr_we_miss     = (grm.csr_we_o !== csr_we);
        mem_req_miss    = grm.mem_req_o !== mem_req;
        mem_we_miss     = grm.mem_we_o !== mem_we;
        //mem_size_miss   = (grm.mem_size_o !== mem_size) & !illegal_instr;
        gpr_we_miss   = grm.gpr_we_o !== gpr_we;
        wb_sel_miss = (grm.wb_sel_o !== wb_sel) & !illegal_instr & !mret;
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end
      default:      //MISC_MEM_OPCODE and other
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
        branch_miss     = grm.branch_o !== branch;
        jal_miss        = grm.jal_o !== jal;
        jalr_miss       = grm.jalr_o !== jalr;
        mret_miss       = grm.mret_o !== mret;
      end
    endcase
  end

  integer X;
  reg [$clog2(cycle+1)-1:0] V;
  integer error;

  initial begin
    $timeformat(-9, 2, " ns", 3);
    error = 0;
  end

  initial begin
    $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
    
    for (V=0; V<cycle/10; V=V+1) begin  // illegal Ð¿Ð¾ 11 Ð² ÐºÐ¾Ð½Ñ†Ðµ opcode
        instr[1:0]  = $random;
        instr[6:2]  = {1'b0,V[1:0],2'b0};
        instr[31:7] = 'b0;
        #delay;
    end
    for (V=0; V<cycle; V=V+1) begin  // illegal Ð¿Ð¾ OP_OPCODE funct7
        instr[11:0]  = {5'b0,OP_OPCODE,2'b11};
        instr[14:12] = V;
        instr[24:15] = $random;
        instr[31:25] = 2**($random % 7);
        #delay;
    end
    for (V=0; V<cycle; V=V+1) begin  // illegal Ð¿Ð¾ SYSTEM_OPCODE
        instr[6:0]  = {SYSTEM_OPCODE,2'b11};
        instr[31:7] = 2**($random % 25);
        #delay;
    end
    instr[6:0]  = {SYSTEM_OPCODE,2'b11};
    instr[31:7] = 25'h604000;
    #delay;
    for (X=0; X<2**10-1; X=X+1) begin
      instr = $random;
      instr[7:0] = {OP_IMM_OPCODE, 2'b11};
      instr[13:12] = 2'b01;
      instr[29:25] = 5'd0;
      instr[31] = 1'b0;
      #delay;
    end
    for (X=0; X<2**10-1; X=X+1) begin
      instr = $random;
      instr[7:0] = {OP_OPCODE, 2'b11};
      instr[29:25] = 5'd0;
      instr[31] = 1'b0;
      #delay;
    end
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
      $display       ("Output 'illegal_instr_o' is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",illegal_instr, grm.illegal_instr_o, instr_type, opcode_type, $time);
      error = error + 1'b1;
      end
    if (~illegal_miss) begin
      if(!illegal_instr) begin
          if (a_sel_miss)begin
            $display ("Output 'a_sel_o'         is incorrect(   %02b instead of    %02b), instruction: %s %s, time: %t",a_sel, grm.a_sel_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
            end
          if (b_sel_miss)begin
            $display ("Output 'b_sel_o'         is incorrect(  %03b instead of   %b), instruction: %s %s, time: %t",b_sel, grm.b_sel_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
            end
          if (alu_op_miss)begin
            $display ("Output 'alu_op_o'        is incorrect(%05b instead of %05b), instruction: %s %s, time: %t",alu_op, grm.alu_op_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
            end
          if (csr_op_miss) begin
            $display ("Output 'csr_op_o'        is incorrect(  %03b instead of   %03b), instruction: %s %s, time: %t",csr_op, grm.csr_op_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
          end
          if (mem_size_miss)begin
            $display ("Output 'mem_size_o'      is incorrect(  %03b instead of   %03b), instruction: %s %s, time: %t",mem_size, grm.mem_size_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
          end
          if (wb_sel_miss)begin
            $display ("Output 'wb_sel_o'        is incorrect(   %02b instead of    %02b), instruction: %s %s, time: %t",wb_sel, grm.wb_sel_o, instr_type, opcode_type, $time);
            error = error + 1'b1;
          end
      end
      if (csr_we_miss) begin
        $display     ("Output 'csr_we_o'        is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",csr_we, grm.csr_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
      end
      if (mem_we_miss)begin
        $display     ("Output 'mem_we_o'        is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",mem_we, grm.mem_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (mem_req_miss)begin
        $display     ("Output 'mem_req_o'       is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",mem_req, grm.mem_req_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (gpr_we_miss)begin
        $display     ("Output 'gpr_we_o'        is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",gpr_we, grm.gpr_we_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (branch_miss)begin
        $display     ("Output 'branch_o'        is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",branch, grm.branch_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (jal_miss)begin
        $display     ("Output 'jal_o'           is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",jal, grm.jal_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (jalr_miss)begin
        $display     ("Output 'jalr_o'          is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",jalr, grm.jalr_o, instr_type, opcode_type, $time);
        error = error + 1'b1;
        end
      if (mret_miss)begin
        $display     ("Output 'mret_o'          is incorrect(    %b instead of     %b), instruction: %s %s, time: %t",mret, grm.mret_o, instr_type, opcode_type, $time);
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

//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Alexey Kozin
// 
// Create Date: 10/08/2023 07:39:15 AM
// Design Name: 
// Module Name: decoder_riscv
// Project Name: RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: main decoder for risc-v processor
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

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

module decoder_riscv_ref (
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
