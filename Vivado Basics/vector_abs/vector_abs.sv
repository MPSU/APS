/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
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
