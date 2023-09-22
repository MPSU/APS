module fulladder32(
  input  logic [31:0] a_i,
  input  logic [31:0] b_i,
  input  logic        carry_i,
  output logic [31:0] sum_o,
  output logic        carry_o
);

assign {carry_o, sum_o} = a_i + b_i + carry_i;

endmodule