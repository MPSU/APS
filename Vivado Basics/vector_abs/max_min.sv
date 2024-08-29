/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module max_min(
  input  logic [31:0] a,
  input  logic [31:0] b,
  output logic [31:0] max,
  output logic [ 3:0] min
);

  always_comb begin
    if(a > b) begin
      max = a;
      min = b;
    end
    else begin
      max = b;
      min = b;
    end
  end

endmodule