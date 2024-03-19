/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Alexander Kharlamov
* Email(s)       : sasha_xarlamov@org.miet.ru

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
  CH_c,
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
  CH_y,
  CH_h,

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
  logic dp;
} Semseg;

module nexys_riscv_unit(
  input  logic        clk_i,
  input  logic        arstn_i,
  input  logic        btnd_i,
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

  riscv_unit unit(
    .clk_i (bufg_clk),
    .rst_i (!arstn_i)
  );

  logic [31:0] instr_addr;
  logic [31:0] instr;
  assign instr_addr = unit.core.instr_addr_o;
  assign instr = unit.core.instr_i;

  import alu_opcodes_pkg::*;

  logic       illegal_instr;

  logic [4:0] opcode;
  assign      opcode = instr[6:2];

  Char op_chars[0:3];
  import riscv_pkg::*;
  always_comb begin
    op_chars = '{4{CH_SPACE}};

    case (opcode)
      LOAD_OPCODE    : op_chars      = '{CH_L, CH_o, CH_A, CH_d};
      MISC_MEM_OPCODE: op_chars      = '{CH_m, CH_i, CH_S, CH_c};
      OP_IMM_OPCODE  : op_chars      = '{CH_o, CH_P, CH_i, CH_m};
      AUIPC_OPCODE   : op_chars      = '{CH_A, CH_u, CH_i, CH_P};
      STORE_OPCODE   : op_chars      = '{CH_S, CH_t, CH_o, CH_r};
      OP_OPCODE      : op_chars[0:1] = '{CH_o, CH_P};
      LUI_OPCODE     : op_chars[0:2] = '{CH_L, CH_u, CH_i};
      BRANCH_OPCODE  : op_chars      = '{CH_b, CH_r, CH_c, CH_h};
      JALR_OPCODE    : op_chars      = '{CH_J, CH_A, CH_L, CH_r};
      JAL_OPCODE     : op_chars[0:2] = '{CH_J, CH_A, CH_L};
      SYSTEM_OPCODE  : op_chars[0:2] = '{CH_S, CH_y, CH_S};

      default        : op_chars[0:2] = '{CH_i, CH_L, CH_L};
    endcase
  end

  Char all_chars[0:7];
  assign all_chars[0:3] = {
      Char'(instr_addr[15:12]),
      Char'(instr_addr[11: 8]),
      Char'(instr_addr[ 7: 4]),
      Char'(instr_addr[ 3: 0])
  };
  assign all_chars[4:7] = op_chars;

  Char current_char;
  logic [7:0] an;
  semseg_one2many #(
    .DATA_T (Char)
  ) semseg_one2many (
    .clk100m_i        (clk_i       ),
    .arstn_i          (arstn_i     ),
    .all_semsegs_i    (all_chars   ),
    .current_semseg_o (current_char),
    .an_o             (an          )
  );

  Semseg current_semseg;
  char2semseg char2semseg (
    .char_i   (current_char  ),
    .semseg_o (current_semseg)
  );

  assign ca_o = current_semseg.ca;
  assign cb_o = current_semseg.cb;
  assign cc_o = current_semseg.cc;
  assign cd_o = current_semseg.cd;
  assign ce_o = current_semseg.ce;
  assign cf_o = current_semseg.cf;
  assign cg_o = current_semseg.cg;
  assign dp_o = current_semseg.dp;

  assign an_o = an;

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
      CH_A    : semseg = ~7'h5F;
      CH_b    : semseg = ~7'h7C;
      CH_c    : semseg = ~7'h58;
      CH_d    : semseg = ~7'h5E;
      CH_E    : semseg = ~7'h79;
      CH_F    : semseg = ~7'h71;
      CH_G    : semseg = ~7'h3D;
      CH_L    : semseg = ~7'h38;
      CH_n    : semseg = ~7'h54;
      CH_o    : semseg = ~7'h5C;
      CH_r    : semseg = ~7'h50;
      CH_S    : semseg = ~7'h64;
      CH_t    : semseg = ~7'h78;
      CH_u    : semseg = ~7'h1C;
      CH_X    : semseg = ~7'h76;
      CH_P    : semseg = ~7'h73;
      CH_J    : semseg = ~7'h1E;
      CH_q    : semseg = ~7'h67;
      CH_i    : semseg = ~7'h30;
      CH_m    : semseg = ~7'h77;
      CH_y    : semseg = ~7'h6E;
      CH_h    : semseg = ~7'h74;
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
  assign semseg_o.dp = 1'b1;

endmodule

module semseg_one2many #(
  parameter int unsigned SEMSEGS_NUM = 8,
  parameter type         DATA_T
) (
  input  DATA_T all_semsegs_i[0:SEMSEGS_NUM-1],
  input  logic  clk100m_i,
  input  logic  arstn_i,
  output DATA_T current_semseg_o,
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

  DATA_T current_semseg;
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
