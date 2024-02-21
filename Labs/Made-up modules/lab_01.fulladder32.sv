/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module fulladder32(
  input  logic [31:0] a_i,
  input  logic [31:0] b_i,
  input  logic        carry_i,
  output logic [31:0] sum_o,
  output logic        carry_o
);

assign {carry_o, sum_o} = a_i + b_i + carry_i;

endmodule