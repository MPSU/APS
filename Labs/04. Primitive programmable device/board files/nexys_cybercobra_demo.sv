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

  CYBERcobra dut (
    .clk_i(btnd_i    ),
    .rst_i(!arstn_i  ),
    .sw_i (sw_i      ),
    .out_o(cobra_out )
  );

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

  logic [31:0] instr_addr;
  logic [31:0] instr;
  assign instr_addr = dut.instr_mem.addr_i;
  assign instr      = dut.instr_mem.read_data_o;

  Instruction_type         instr_type;
  logic [ALU_OP_WIDTH-1:0] alu_op;
  logic                    illegal_instr;
  nexys_CYBERcobra_decoder nexys_CYBERcobra_decoder (
    .instr_i         (instr        ),
    .instr_type_o    (instr_type   ),
    .alu_op_o        (alu_op       ),
    .illegal_instr_o (illegal_instr)
  );

  Char [1:0] instr_type_chars;
  always_comb begin
    instr_type_chars = {2{CH_SPACE}};

    unique case (instr_type)
      INSTR_COMPUTATIONAL: instr_type_chars = {CH_C, CH_P};
      INSTR_BRANCH       : instr_type_chars = {CH_b, CH_r};
      INSTR_CONST        : instr_type_chars = {CH_C, CH_n};
      INSTR_PERIPHERY    : instr_type_chars = {CH_P, CH_E};
      INSTR_JUMP         : instr_type_chars = {CH_J, CH_u};
      INSTR_NOP          : instr_type_chars = {CH_n, CH_o};
    endcase

    if (illegal_instr) instr_type_chars = {CH_i, CH_L};
  end

  import alu_opcodes_pkg::*;

  Char [3:0] alu_op_chars;
  always_comb begin
    alu_op_chars = {4{CH_SPACE}};

    case (alu_op)
      ALU_ADD : alu_op_chars[3:1] = {CH_A, CH_d, CH_d};
      ALU_SUB : alu_op_chars[3:1] = {CH_S, CH_u, CH_b};
      ALU_XOR : alu_op_chars[3:1] = {CH_X, CH_o, CH_r};
      ALU_OR  : alu_op_chars[3:2] = {CH_o, CH_r};
      ALU_AND : alu_op_chars[3:1] = {CH_A, CH_n, CH_d};
      ALU_SRA : alu_op_chars[3:1] = {CH_S, CH_r, CH_A};
      ALU_SRL : alu_op_chars[3:1] = {CH_S, CH_r, CH_L};
      ALU_SLL : alu_op_chars[3:1] = {CH_S, CH_L, CH_L};
      ALU_LTS : alu_op_chars[3:1] = {CH_L, CH_t, CH_S};
      ALU_LTU : alu_op_chars[3:1] = {CH_L, CH_t, CH_u};
      ALU_GES : alu_op_chars[3:1] = {CH_G, CH_E, CH_S};
      ALU_GEU : alu_op_chars[3:1] = {CH_G, CH_E, CH_u};
      ALU_EQ  : alu_op_chars[3:2] = {CH_E, CH_q};
      ALU_NE  : alu_op_chars[3:2] = {CH_n, CH_E};
      ALU_SLTS: alu_op_chars      = {CH_S, CH_L, CH_t, CH_S};
      ALU_SLTU: alu_op_chars      = {CH_S, CH_L, CH_t, CH_u};

      default : ;
    endcase
  end

  Char [7:0] all_chars;
  assign all_chars = {
      Char'(instr_addr[7:4]),
      Char'(instr_addr[3:0]),
      instr_type_chars,
      alu_op_chars
  };

  typedef struct {
    logic ca;
    logic cb;
    logic cc;
    logic cd;
    logic ce;
    logic cf;
    logic cg;
  } Semseg;
  Semseg all_semsegs[0:7];

  for (genvar semseg_num = 0; semseg_num < 8; ++semseg_num) begin : CHAR2SEMSEG_GEN
    char2semseg char2semseg (
      .char_i (all_chars[semseg_num]     ),
      .ca_o   (all_semsegs[semseg_num].ca),
      .cb_o   (all_semsegs[semseg_num].cb),
      .cc_o   (all_semsegs[semseg_num].cc),
      .cd_o   (all_semsegs[semseg_num].cd),
      .ce_o   (all_semsegs[semseg_num].ce),
      .cf_o   (all_semsegs[semseg_num].cf),
      .cg_o   (all_semsegs[semseg_num].cg)
    );
  end

  Semseg current_semseg;
  always_comb begin
    unique case (1'b0)
      an_ff[0]: current_semseg = all_semsegs[0];
      an_ff[1]: current_semseg = all_semsegs[1];
      an_ff[2]: current_semseg = all_semsegs[2];
      an_ff[3]: current_semseg = all_semsegs[3];
      an_ff[4]: current_semseg = all_semsegs[4];
      an_ff[5]: current_semseg = all_semsegs[5];
      an_ff[6]: current_semseg = all_semsegs[6];
      an_ff[7]: current_semseg = all_semsegs[7];
    endcase
  end

  assign ca_o = current_semseg.ca;
  assign cb_o = current_semseg.cb;
  assign cc_o = current_semseg.cc;
  assign cd_o = current_semseg.cd;
  assign ce_o = current_semseg.ce;
  assign cf_o = current_semseg.cf;
  assign cg_o = current_semseg.cg;
  assign dp_o = 1'b1;

  assign an_o = an_ff;

  assign led_o = cobra_out[15:0];

endmodule

module nexys_CYBERcobra_decoder (
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
  input  Char  char_i,
  output logic ca_o,
  output logic cb_o,
  output logic cc_o,
  output logic cd_o,
  output logic ce_o,
  output logic cf_o,
  output logic cg_o
);

  localparam bit [6:0] BLANK = '1;

  logic [6:0] hex;
  always_comb begin
    unique case (char_i[3:0])
      4'h0: hex = 7'h3F;
      4'h1: hex = 7'h06;
      4'h2: hex = 7'h5B;
      4'h3: hex = 7'h4F;
      4'h4: hex = 7'h66;
      4'h5: hex = 7'h6D;
      4'h6: hex = 7'h7D;
      4'h7: hex = 7'h07;
      4'h8: hex = 7'h7F;
      4'h9: hex = 7'h6F;
      4'hA: hex = 7'h77;
      4'hb: hex = 7'h7C;
      4'hC: hex = 7'h39;
      4'hd: hex = 7'h5E;
      4'hE: hex = 7'h79;
      4'hF: hex = 7'h71;
      default: hex = BLANK;
    endcase
  end

if (!HEX_ONLY) begin : HEX_ONLY_CHARS_GEN
  logic [6:0] other_chars;
  always_comb begin
    case (char_i)
      CH_G    : other_chars = 7'h3D;
      CH_L    : other_chars = 7'h38;
      CH_n    : other_chars = 7'h54;
      CH_o    : other_chars = 7'h5C;
      CH_r    : other_chars = 7'h50;
      CH_S    : other_chars = 7'h6D;
      CH_t    : other_chars = 7'h78;
      CH_u    : other_chars = 7'h1C;
      CH_X    : other_chars = 7'h49;
      CH_P    : other_chars = 7'h73;
      CH_J    : other_chars = 7'h1E;
      CH_q    : other_chars = 7'h67;
      CH_i    : other_chars = 7'h04;
      default : other_chars = BLANK;
    endcase
  end

  assign {cg_o, cf_o, ce_o, cd_o, cc_o, cb_o, ca_o} = hex & other_chars;
end else begin : ALL_CHARS
  assign {cg_o, cf_o, ce_o, cd_o, cc_o, cb_o, ca_o} = hex;
end

endmodule
