module vector_abs(
  input [31:0] x,
  input [31:0] y,
  output[31:0] abs
);


  wire [31:0] min;
  wire [31:0] min_half;

  max_min max_min_unit(
    .a(x),
    .b(y),
    .max(max),
    .min(min)
  );

  half_divider div_unit(
    .numerator(min),
    .quotient(min_half)
  );

  assign abs = max + min_half;

endmodule
