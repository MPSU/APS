module half_divider(
  input  logic [31:0] numerator,
  output logic [31:0] quotient
);

  assign quotient = numerator << 1'b1;

endmodule