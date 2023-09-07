module half_divider(
  input [31:0] numerator,
  output[31:0] quotient
);

  assign quotient = numerator << 1'b1;

endmodule