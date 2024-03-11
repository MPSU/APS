/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

typedef enum {
  INSTR_COMPUTATIONAL, // computational
  INSTR_BRANCH,
  INSTR_CONST,         // const load
  INSTR_PERIPHERY,     // periphery load
  INSTR_JUMP,
  INSTR_NOP            // ws == 3
} Instruction_type;

typedef enum {
  CH_0 = 0,
  CH_1,
  CH_2,
  CH_3,
  CH_4,
  CH_5,
  CH_6,
  CH_7,
  CH_8,
  CH_9,
  CH_A,
  CH_b,
  CH_C,
  CH_d,
  CH_E,
  CH_F,
  CH_G,
  CH_L,
  CH_n,
  CH_o,
  CH_r,
  CH_S,
  CH_t,
  CH_u,
  CH_X,
  CH_P,
  CH_J,
  CH_q,
  CH_i,

  CH_SPACE
} Char;

typedef struct {
  logic ca;
  logic cb;
  logic cc;
  logic cd;
  logic ce;
  logic cf;
  logic cg;
} Semseg;

module nexys_CYBERcobra(
  input  logic        clk_i,
  input  logic        arstn_i,
  input  logic [15:0] sw_i,
  input  logic        btnd_i,
  output logic [15:0] led_o,
  output logic        ca_o,
  output logic        cb_o,
  output logic        cc_o,
  output logic        cd_o,
  output logic        ce_o,
  output logic        cf_o,
  output logic        cg_o,
  output logic        dp_o,
  output logic [ 7:0] an_o
);

  logic [31:0] cobra_out;

  logic btnd;
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) btnd <= 1'b0;
    else          btnd <= btnd_i;
  end

  CYBERcobra dut (
    .clk_i (btnd     ),
    .rst_i (!arstn_i ),
    .sw_i  (sw_i     ),
    .out_o (cobra_out)
  );

  logic [31:0] instr_addr;
  logic [31:0] instr;
  assign instr_addr = dut.pc;
  assign instr      = dut.instr;

  import alu_opcodes_pkg::*;

  Instruction_type         instr_type;
  logic [ALU_OP_WIDTH-1:0] alu_op;
  logic                    illegal_instr;
  nexys_CYBERcobra_decoder nexys_CYBERcobra_decoder (
    .instr_i         (instr        ),
    .instr_type_o    (instr_type   ),
    .alu_op_o        (alu_op       ),
    .illegal_instr_o (illegal_instr)
  );

  Char instr_type_chars[0:1];
  always_comb begin
    instr_type_chars = '{2{CH_SPACE}};

    unique case (instr_type)
      INSTR_COMPUTATIONAL: instr_type_chars = '{CH_C, CH_P};
      INSTR_BRANCH       : instr_type_chars = '{CH_b, CH_r};
      INSTR_CONST        : instr_type_chars = '{CH_C, CH_n};
      INSTR_PERIPHERY    : instr_type_chars = '{CH_P, CH_E};
      INSTR_JUMP         : instr_type_chars = '{CH_J, CH_u};
      INSTR_NOP          : instr_type_chars = '{CH_n, CH_o};
    endcase

    if (illegal_instr) instr_type_chars = '{CH_i, CH_L};
  end

  Char alu_op_chars[0:3];
  always_comb begin
    alu_op_chars = '{4{CH_SPACE}};

    case (alu_op)
      ALU_ADD : alu_op_chars[0:2] = '{CH_A, CH_d, CH_d};
      ALU_SUB : alu_op_chars[0:2] = '{CH_S, CH_u, CH_b};
      ALU_XOR : alu_op_chars[0:2] = '{CH_X, CH_o, CH_r};
      ALU_OR  : alu_op_chars[0:1] = '{CH_o, CH_r};
      ALU_AND : alu_op_chars[0:2] = '{CH_A, CH_n, CH_d};
      ALU_SRA : alu_op_chars[0:2] = '{CH_S, CH_r, CH_A};
      ALU_SRL : alu_op_chars[0:2] = '{CH_S, CH_r, CH_L};
      ALU_SLL : alu_op_chars[0:2] = '{CH_S, CH_L, CH_L};
      ALU_LTS : alu_op_chars[0:2] = '{CH_L, CH_t, CH_S};
      ALU_LTU : alu_op_chars[0:2] = '{CH_L, CH_t, CH_u};
      ALU_GES : alu_op_chars[0:2] = '{CH_G, CH_E, CH_S};
      ALU_GEU : alu_op_chars[0:2] = '{CH_G, CH_E, CH_u};
      ALU_EQ  : alu_op_chars[0:1] = '{CH_E, CH_q};
      ALU_NE  : alu_op_chars[0:1] = '{CH_n, CH_E};
      ALU_SLTS: alu_op_chars      = '{CH_S, CH_L, CH_t, CH_S};
      ALU_SLTU: alu_op_chars      = '{CH_S, CH_L, CH_t, CH_u};

      default : ;
    endcase
  end

  Char all_chars[0:7];
  assign all_chars = {
      Char'(instr_addr[7:4]),
      Char'(instr_addr[3:0]),
      instr_type_chars,
      alu_op_chars
  };

  Semseg all_semsegs[0:7];

  for (genvar semseg_num = 0; semseg_num < 8; ++semseg_num) begin : CHAR2SEMSEG_GEN
    char2semseg char2semseg (
      .char_i   (all_chars  [semseg_num]),
      .semseg_o (all_semsegs[semseg_num])
    );
  end

  Semseg current_semseg;
  logic [7:0] an;
  semseg_one2many semseg_one2many (
    .clk100m_i        (clk_i         ),
    .arstn_i          (arstn_i       ),
    .all_semsegs_i    (all_semsegs   ),
    .current_semseg_o (current_semseg),
    .an_o             (an            )
  );

  assign ca_o = current_semseg.ca;
  assign cb_o = current_semseg.cb;
  assign cc_o = current_semseg.cc;
  assign cd_o = current_semseg.cd;
  assign ce_o = current_semseg.ce;
  assign cf_o = current_semseg.cf;
  assign cg_o = current_semseg.cg;
  assign dp_o = 1'b1;

  assign an_o = an;

  assign led_o = cobra_out[15:0];

endmodule

module nexys_CYBERcobra_decoder
  import alu_opcodes_pkg::*;
(
  input  logic [31:0]             instr_i,
  output Instruction_type         instr_type_o,
  output logic [ALU_OP_WIDTH-1:0] alu_op_o,
  output logic                    illegal_instr_o
);

  logic       j;
  logic       b;
  logic [1:0] ws;

  assign j  = instr_i[31];
  assign b  = instr_i[30];
  assign ws = instr_i[29:28];

  always_comb begin
    instr_type_o    = INSTR_NOP;

    if (j) begin
      instr_type_o = INSTR_JUMP;
    end else if (b) begin
      instr_type_o = INSTR_BRANCH;
    end else begin
      case (ws)
        2'd0: instr_type_o    = INSTR_CONST;
        2'd1: instr_type_o    = INSTR_COMPUTATIONAL;
        2'd2: instr_type_o    = INSTR_PERIPHERY;
        2'd3: instr_type_o    = INSTR_NOP;
      endcase
    end
  end

  assign alu_op_o        = instr_i[27:23];

  import alu_opcodes_pkg::*;

  assign illegal_instr_o = (instr_type_o inside {INSTR_COMPUTATIONAL, INSTR_BRANCH}) &&
      !(alu_op_o inside{
          ALU_ADD ,
          ALU_SUB ,
          ALU_XOR ,
          ALU_OR  ,
          ALU_AND ,
          ALU_SRA ,
          ALU_SRL ,
          ALU_SLL ,
          ALU_LTS ,
          ALU_LTU ,
          ALU_GES ,
          ALU_GEU ,
          ALU_EQ  ,
          ALU_NE  ,
          ALU_SLTS,
          ALU_SLTU});
endmodule

module char2semseg #(
  parameter bit HEX_ONLY = 1'b0
) (
  input  Char   char_i,
  output Semseg semseg_o
);

  localparam bit [6:0] BLANK = '1;

  logic [6:0] semseg;
  always_comb begin
    case (char_i)
      CH_0    : semseg = ~7'h3F;
      CH_1    : semseg = ~7'h06;
      CH_2    : semseg = ~7'h5B;
      CH_3    : semseg = ~7'h4F;
      CH_4    : semseg = ~7'h66;
      CH_5    : semseg = ~7'h6D;
      CH_6    : semseg = ~7'h7D;
      CH_7    : semseg = ~7'h07;
      CH_8    : semseg = ~7'h7F;
      CH_9    : semseg = ~7'h6F;
      CH_A    : semseg = ~7'h77;
      CH_b    : semseg = ~7'h7C;
      CH_C    : semseg = ~7'h39;
      CH_d    : semseg = ~7'h5E;
      CH_E    : semseg = ~7'h79;
      CH_F    : semseg = ~7'h71;
      CH_G    : semseg = ~7'h3D;
      CH_L    : semseg = ~7'h38;
      CH_n    : semseg = ~7'h54;
      CH_o    : semseg = ~7'h5C;
      CH_r    : semseg = ~7'h50;
      CH_S    : semseg = ~7'h6D;
      CH_t    : semseg = ~7'h78;
      CH_u    : semseg = ~7'h1C;
      CH_X    : semseg = ~7'h49;
      CH_P    : semseg = ~7'h73;
      CH_J    : semseg = ~7'h1E;
      CH_q    : semseg = ~7'h67;
      CH_i    : semseg = ~7'h04;
      default : semseg = BLANK;
    endcase
  end

  assign semseg_o.ca = semseg[0];
  assign semseg_o.cb = semseg[1];
  assign semseg_o.cc = semseg[2];
  assign semseg_o.cd = semseg[3];
  assign semseg_o.ce = semseg[4];
  assign semseg_o.cf = semseg[5];
  assign semseg_o.cg = semseg[6];

endmodule

module semseg_one2many #(
  parameter int unsigned SEMSEGS_NUM = 8
) (
  input  Semseg all_semsegs_i[0:SEMSEGS_NUM-1],
  input  logic  clk100m_i,
  input  logic  arstn_i,
  output Semseg current_semseg_o,
  output logic [7:0] an_o
);
  logic  clk_i;
  assign clk_i = clk100m_i;

  localparam int COUNTER_WIDTH = 10;
  logic [COUNTER_WIDTH-1:0] counter_next;
  logic [COUNTER_WIDTH-1:0] counter_ff;
  assign counter_next = counter_ff + COUNTER_WIDTH'('b1);
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) counter_ff <= '0;
    else          counter_ff <= counter_next;
  end

  logic [7:0] an_ff;
  logic [7:0] an_next;
  logic       an_en;
  assign an_next = {an_ff[$left(an_ff)-1:0], an_ff[$left(an_ff)]};
  assign an_en   = ~|counter_ff;
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if      (!arstn_i) an_ff <= ~8'b1;
    else if (an_en)    an_ff <= an_next;
  end

  Semseg current_semseg;
  always_comb begin
    unique case (1'b0)
      an_ff[0]: current_semseg = all_semsegs_i[7];
      an_ff[1]: current_semseg = all_semsegs_i[6];
      an_ff[2]: current_semseg = all_semsegs_i[5];
      an_ff[3]: current_semseg = all_semsegs_i[4];
      an_ff[4]: current_semseg = all_semsegs_i[3];
      an_ff[5]: current_semseg = all_semsegs_i[2];
      an_ff[6]: current_semseg = all_semsegs_i[1];
      an_ff[7]: current_semseg = all_semsegs_i[0];
    endcase
  end

  assign current_semseg_o = current_semseg;

  assign an_o = an_ff;

endmodule
