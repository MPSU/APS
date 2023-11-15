module vector_abs(
  input  logic [31:0] x,
  input  logic [31:0] y,
  output logic [31:0] abs
);


  logic [31:0] min;
  logic [31:0] min_half;

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
