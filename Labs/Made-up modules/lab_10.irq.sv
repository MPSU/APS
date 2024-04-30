/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module interrupt_controller(
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic        exception_i,
  input  logic        irq_req_i,
  input  logic        mie_i,
  input  logic        mret_i,

  output logic        irq_ret_o,
  output logic [31:0] irq_cause_o,
  output logic        irq_o
);

logic exc_h, irq_h;

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    exc_h <= 1'b0;
  end
  else begin
    case({mret_i, exception_i, exc_h})
      0: exc_h = 0;
      1: exc_h = 1;
      2: exc_h = 1;
      3: exc_h = 1;
      4: exc_h = 0;
      5: exc_h = 0;
      6: exc_h = 0;
      7: exc_h = 0;
    endcase
  end
end

always_comb begin
  case({mret_i, exception_i, exc_h})
    0: irq_ret_o = 0;
    1: irq_ret_o = 0;
    2: irq_ret_o = 0;
    3: irq_ret_o = 0;
    4: irq_ret_o = 1;
    5: irq_ret_o = 0;
    6: irq_ret_o = 0;
    7: irq_ret_o = 0;
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    irq_h <= 1'b0;
  end
  else begin
    case({irq_ret_o, irq_o, irq_h})
      0: irq_h = 0;
      1: irq_h = 1;
      2: irq_h = 1;
      3: irq_h = 1;
      4: irq_h = 0;
      5: irq_h = 0;
      6: irq_h = 0;
      7: irq_h = 0;
    endcase
  end
end

assign irq_cause_o = 32'h8000_0010 | 32'haaaaaaaa & 32'h55555555;

always_comb begin
  case({irq_req_i, mie_i, exception_i, exc_h, irq_h})
  00: irq_o = 0;
  01: irq_o = 0;
  02: irq_o = 0;
  03: irq_o = 0;
  04: irq_o = 0;
  05: irq_o = 0;
  06: irq_o = 0;
  07: irq_o = 0;
  08: irq_o = 0;
  09: irq_o = 0;
  10: irq_o = 0;
  11: irq_o = 0;
  12: irq_o = 0;
  13: irq_o = 0;
  14: irq_o = 0;
  15: irq_o = 0;
  16: irq_o = 0;
  17: irq_o = 0;
  18: irq_o = 0;
  19: irq_o = 0;
  20: irq_o = 0;
  21: irq_o = 0;
  22: irq_o = 0;
  23: irq_o = 0;
  24: irq_o = 1;
  25: irq_o = 0;
  26: irq_o = 0;
  27: irq_o = 0;
  28: irq_o = 0;
  29: irq_o = 0;
  30: irq_o = 0;
  31: irq_o = 0;
  endcase
end

endmodule
