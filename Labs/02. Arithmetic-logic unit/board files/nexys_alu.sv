module nexys_alu(
  input  logic        clk_i,
  input  logic        arstn_i,
  input  logic [15:0] sw_i,
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
  logic sign_on;
  assign sign_on = sw_i[5];

  logic sext_operand_a;
  assign sext_operand_a = sign_on;
  logic sext_operand_b;
  assign sext_operand_b = sign_on;

  import alu_opcodes_pkg::*;

  logic [4:0] operator;
  assign      operator = sw_i[4:0];

  logic [31:0]              operand_b;
  always_comb begin
    operand_b = {27'b0, sw_i[10:6]};
    if (sext_operand_b) operand_b = {{28{operand_b[4]}}, operand_b[3:0]};
  end

  logic [31:0]              operand_a;
  always_comb begin
    operand_a = {27'b0, sw_i[15:11]};
    if (sext_operand_a) operand_a = {{28{operand_a[4]}}, operand_a[3:0]};
  end

  logic [31:0]              result;
  logic                     flag;

  alu_riscv alu_riscv (
    .alu_op_i (operator),
    .a_i      (operand_a),
    .b_i      (operand_b),

    .result_o (result),
    .flag_o   (flag)
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
  always_ff @(posedge clk_i) begin
    if      (!arstn_i) an_ff <= ~8'b1;
    else if (an_en)    an_ff <= an_next;
  end

  function automatic logic [6:0] hex2semseg(input logic [3:0] hex);
      unique case (hex)
        4'h0: return 7'b0000001;
        4'h1: return 7'b1001111;
        4'h2: return 7'b0010010;
        4'h3: return 7'b0000110;
        4'h4: return 7'b1001100;
        4'h5: return 7'b0100100;
        4'h6: return 7'b0100000;
        4'h7: return 7'b0001111;
        4'h8: return 7'b0000000;
        4'h9: return 7'b0000100;
        4'hA: return 7'b0001000;
        4'hB: return 7'b1100000;
        4'hC: return 7'b0110001;
        4'hD: return 7'b1000010;
        4'hE: return 7'b0110000;
        4'hF: return 7'b0111000;
      endcase
  endfunction

  logic  is_result_negative;
  assign is_result_negative = result[$left(result)] & sign_on;
  logic  is_operand_a_negative;
  assign is_operand_a_negative = operand_a[$left(operand_a)];
  logic  is_operand_b_negative;
  assign is_operand_b_negative = operand_b[$left(operand_b)];

  logic [11:0] result_sign_regard;
  assign result_sign_regard    = is_result_negative    ? (~result[11:0] + 12'b1)  : (result[11:0]);
  logic [ 4:0] operand_a_sign_regard;
  assign operand_a_sign_regard = is_operand_a_negative ? (~operand_a[4:0] + 5'b1) : (operand_a[4:0]);
  logic [ 4:0] operand_b_sign_regard;
  assign operand_b_sign_regard = is_operand_b_negative ? (~operand_b[4:0] + 5'b1) : (operand_b[4:0]);

  localparam bit [6:0] MINUS = 7'b1111110;
  localparam bit [6:0] BLANK = 7'b1111111;

  logic [ 6:0] semseg;
  always_comb begin
    semseg = BLANK;

    unique case (1'b0)
      an_ff[0]: semseg = hex2semseg(result_sign_regard[ 3:0]);
      an_ff[1]: semseg = hex2semseg(result_sign_regard[ 7:4]);
      an_ff[2]: semseg = hex2semseg(result_sign_regard[11:8]);
      an_ff[3]: semseg = is_result_negative ? MINUS : BLANK;
      an_ff[4]: semseg = hex2semseg(operand_b_sign_regard[3:0]);
      an_ff[5]: semseg = (is_operand_b_negative ? MINUS : BLANK) & (operand_b_sign_regard[4] ? hex2semseg(4'b1) : BLANK);
      an_ff[6]: semseg = hex2semseg(operand_a_sign_regard[3:0]);
      an_ff[7]: semseg = (is_operand_a_negative ? MINUS : BLANK) & (operand_a_sign_regard[4] ? hex2semseg(4'b1) : BLANK);
    endcase
  end

  assign {ca_o, cb_o, cc_o, cd_o, ce_o, cf_o, cg_o} = semseg;
  assign dp_o = an_ff[6] ? 1'b1 : 1'b0;

  assign led_o[14:0] = result[14:0];
  assign led_o[15]   = flag;

  assign an_o = an_ff;

endmodule
