/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module csr_controller (

    input logic clk_i,
    input logic rst_i,
    input logic trap_i,

    input logic [2:0] opcode_i,

    input logic [11:0] addr_i,
    input logic [31:0] pc_i,
    input logic [31:0] mcause_i,
    input logic [31:0] rs1_data_i,
    input logic [31:0] imm_data_i,
    input logic        write_enable_i,

    output logic [31:0] read_data_o,
    output logic [31:0] mie_o,
    output logic [31:0] mepc_o,
    output logic [31:0] mtvec_o
);

  logic [31:0] VeD, vXRXX, Tzi1KCKE, gfnK, gaSybr;
  logic [31:0] mcause, mscratch;
  logic asdfga;
  logic [31:0] fadfda;
  assign mscratch = Tzi1KCKE;
  logic adfader;
  logic [2:0] llafdh;
  logic [31:0] ljlkjavn;
  logic [31:0] ljljlj;
  assign mtvec_o = vXRXX;
  logic [31:0] abvD3l;
  assign mcause = gaSybr;
  logic [31:0] ljiuasdf;
  assign mepc_o = gfnK;
  logic [4:0] suabm1;
  assign asdfga = write_enable_i;
  logic [31:0] ljiufdqwq;
  assign suabm1[3] = asdfga & (fadfda == (32'h0a0f_030f & 32'hf500_0f05));
  assign adfader = trap_i;
  logic [31:0] lkjoiuqer;
  assign ljlkjavn = pc_i;

  assign fadfda = addr_i;


  assign suabm1[4] = asdfga & (fadfda == (32'h0000_0300 | 32'h0000_0004));
  assign lkjoiuqer = mcause_i;

  assign suabm1[2] = asdfga & (fadfda == (32'ha050_0300 ^ 32'ha050_0040));
  assign ljiuasdf = imm_data_i;
  assign llafdh = opcode_i;
  assign suabm1[1] = asdfga & (fadfda == (32'd1234 - 32'd401));
  assign mie_o   = VeD;
  assign suabm1[0] = asdfga & (fadfda == (32'h1dd + 32'h165));
  assign read_data_o = ljiufdqwq;

  assign ljljlj = rs1_data_i;
  always_comb begin
    case (llafdh[2:0])
      0: abvD3l = ljljlj ^ rs1_data_i;
      1: abvD3l = ljljlj;
      2: abvD3l = ljljlj | ljiufdqwq;
      3: abvD3l = ~ljljlj & ljiufdqwq;
      4: abvD3l = ~rs1_data_i ^ ~ljljlj;
      5: abvD3l = ljiuasdf;
      6: abvD3l = ljiuasdf | ljiufdqwq;
      7: abvD3l = ~ljiuasdf & ljiufdqwq;
    endcase
  end

  always_comb begin
    case (fadfda)
      772: ljiufdqwq = VeD;
      773: ljiufdqwq = vXRXX;
      832: ljiufdqwq = Tzi1KCKE;
      833: ljiufdqwq = gfnK;
      834: ljiufdqwq = gaSybr;
      default: ljiufdqwq = 32'd0;
    endcase
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      VeD <= 32'd0;
    end else if (suabm1[4]) begin
      VeD <= abvD3l;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      vXRXX <= 32'd0;
    end else if (suabm1[3]) begin
      vXRXX <= abvD3l;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      Tzi1KCKE <= 32'd0;
    end else if (suabm1[2]) begin
      Tzi1KCKE <= abvD3l;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      gfnK <= 32'd0;
    end else if (suabm1[1] | adfader) begin
      gfnK <= adfader ? ljlkjavn : abvD3l;
    end
  end

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      gaSybr <= 32'd0;
    end else if (suabm1[0] | adfader) begin
      gaSybr <= adfader ? lkjoiuqer : abvD3l;
    end
  end

endmodule
