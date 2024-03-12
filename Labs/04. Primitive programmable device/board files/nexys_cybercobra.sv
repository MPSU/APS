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
  INSTR_ALU   , // branch and computational
  INSTR_LI    , // const load
  INSTR_IN    , // periphery load
  INSTR_JUMP  ,
  INSTR_NOP     // ws == 3
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
  CH_m,

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

  logic btnd_sync;
  sync sync (
    .clk_i             ,
    .data_i (btnd_i   ),
    .data_o (btnd_sync)
  );
  logic btnd_debounce;
  debounce debounce (
    .clk_i                 ,
    .arstn_i               ,
    .data_i (btnd_sync    ),
    .data_o (btnd_debounce)
  );
  logic bufg_clk;
  BUFG dut_bufg(
    .I (btnd_debounce),
    .O (bufg_clk     )
  );

  CYBERcobra dut (
    .clk_i (bufg_clk     ),
    .rst_i (!arstn_i     ),
    .sw_i  (sw_i         ),
    .out_o (cobra_out    )
  );

  logic [31:0] instr_addr;
  logic [31:0] instr;
  assign instr_addr = dut.instr_mem.addr_i;
  assign instr      = dut.instr_mem.read_data_o;

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

  Char op_chars[0:3];
  always_comb begin
    op_chars = '{4{CH_SPACE}};

    case (instr_type)
      INSTR_ALU:
        case (alu_op)
          ALU_ADD : op_chars[0:2] = '{CH_A, CH_d, CH_d};
          ALU_SUB : op_chars[0:2] = '{CH_S, CH_u, CH_b};
          ALU_XOR : op_chars[0:2] = '{CH_X, CH_o, CH_r};
          ALU_OR  : op_chars[0:1] = '{CH_o, CH_r};
          ALU_AND : op_chars[0:2] = '{CH_A, CH_n, CH_d};
          ALU_SRA : op_chars[0:2] = '{CH_S, CH_r, CH_A};
          ALU_SRL : op_chars[0:2] = '{CH_S, CH_r, CH_L};
          ALU_SLL : op_chars[0:2] = '{CH_S, CH_L, CH_L};
          ALU_LTS : op_chars[0:2] = '{CH_L, CH_t, CH_S};
          ALU_LTU : op_chars[0:2] = '{CH_L, CH_t, CH_u};
          ALU_GES : op_chars[0:2] = '{CH_G, CH_E, CH_S};
          ALU_GEU : op_chars[0:2] = '{CH_G, CH_E, CH_u};
          ALU_EQ  : op_chars[0:1] = '{CH_E, CH_q};
          ALU_NE  : op_chars[0:1] = '{CH_n, CH_E};
          ALU_SLTS: op_chars      = '{CH_S, CH_L, CH_t, CH_S};
          ALU_SLTU: op_chars      = '{CH_S, CH_L, CH_t, CH_u};

          default : ;
        endcase
      INSTR_LI  : op_chars[0:1] = '{CH_L, CH_i};
      INSTR_JUMP: op_chars      = '{CH_J, CH_u, CH_m, CH_P};
      INSTR_NOP : op_chars[0:2] = '{CH_n, CH_o, CH_P};
      INSTR_IN  : op_chars[0:1] = '{CH_i, CH_n};
    endcase
    if (illegal_instr) op_chars[0:2] = '{CH_i, CH_L, CH_L};
  end

  Char all_chars[0:7];
  assign all_chars[0:3] = {
      Char'(led_o[15:8])    ,
      Char'(led_o[ 7:0])    ,
      Char'(instr_addr[7:4]),
      Char'(instr_addr[3:0])
  };
  assign all_chars[4:7] = op_chars;

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

  logic  is_branch_instr;
  assign is_branch_instr = b;

  always_comb begin
    instr_type_o    = INSTR_NOP;

    if (j) begin
      instr_type_o = INSTR_JUMP;
    end else if (b) begin
      instr_type_o    = INSTR_ALU;
    end else begin
      case (ws)
        2'd0: instr_type_o    = INSTR_LI;
        2'd1: instr_type_o    = INSTR_ALU;
        2'd2: instr_type_o    = INSTR_IN;
        2'd3: instr_type_o    = INSTR_NOP;
      endcase
    end
  end

  assign alu_op_o        = instr_i[27:23];

  import alu_opcodes_pkg::*;

  typedef enum {
    ALU_OP_BRANCH,
    ALU_OP_COMPUTATIONAL,
    ALU_OP_ILLEGAL
  } Alu_op_type;
  Alu_op_type alu_op_type;
  always_comb begin
    alu_op_type = ALU_OP_ILLEGAL;

    case (alu_op_o) inside
      ALU_LTS,
      ALU_LTU,
      ALU_GES,
      ALU_GEU,
      ALU_EQ ,
      ALU_NE : alu_op_type = ALU_OP_BRANCH;

      ALU_ADD ,
      ALU_SUB ,
      ALU_XOR ,
      ALU_OR  ,
      ALU_AND ,
      ALU_SRA ,
      ALU_SRL ,
      ALU_SLL ,
      ALU_SLTS,
      ALU_SLTU: alu_op_type = ALU_OP_COMPUTATIONAL;

      default : alu_op_type = ALU_OP_ILLEGAL;
    endcase
  end

  assign illegal_instr_o = (instr_type_o == INSTR_ALU) && ((alu_op_type == ALU_OP_ILLEGAL) ||
      ((alu_op_type == ALU_OP_BRANCH) ^ is_branch_instr));
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
      CH_m    : semseg = ~7'h55;
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

module debounce #(
  parameter int unsigned MAX_COUNT = 10000
) (
  input  logic clk_i,
  input  logic arstn_i,
  input  logic data_i,
  output logic data_o
);

  localparam int COUNTER_WIDTH = $clog2(MAX_COUNT);
  logic [COUNTER_WIDTH-1:0] counter_next;
  logic [COUNTER_WIDTH-1:0] counter_ff;
  assign counter_next = (data_o != data_i) ? counter_ff - COUNTER_WIDTH'('b1) :
                                             COUNTER_WIDTH'(MAX_COUNT);
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if      (!arstn_i)         counter_ff <= COUNTER_WIDTH'(MAX_COUNT);
    else                       counter_ff <= counter_next;
  end

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if      (!arstn_i)     data_o <= '0;
    else if (~|counter_ff) data_o <= data_i;
  end

endmodule

module sync #(
  parameter int unsigned SYNC_STAGES = 3
) (
  input  logic clk_i,
  input  logic data_i,
  output logic data_o
);

  logic [SYNC_STAGES-1:0] sync_buffer_ff;
  logic [SYNC_STAGES-1:0] sync_buffer_next;
  assign                  sync_buffer_next = {sync_buffer_ff[$left(sync_buffer_ff)-1:0], data_i};
  always_ff @(posedge clk_i) begin
    sync_buffer_ff <= sync_buffer_next;
  end

  assign data_o = sync_buffer_ff[$left(sync_buffer_ff)];

endmodule
