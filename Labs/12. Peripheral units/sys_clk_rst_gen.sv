module sys_clk_rst_gen#(
  parameter DIV_WIDTH = 4
)(
    input  logic                  ex_clk_i,
    input  logic                  ex_areset_n_i,
    input  logic [DIV_WIDTH-1:0]  div_i,

    output logic                  sys_clk_o,
    output logic                  sys_reset_o
);

logic [1:0] ex_arstn_buf;
logic [DIV_WIDTH-1:0] sys_rstn_buf;

logic ex_arstn_buffered;
assign ex_arstn_buffered = ex_arstn_buf[1];
assign sys_reset_o = !sys_rstn_buf[DIV_WIDTH-1];

always_ff @(posedge ex_clk_i or negedge ex_areset_n_i) begin
  if(!ex_areset_n_i) begin
    ex_arstn_buf <= 2'b0;
  end
  else begin
    ex_arstn_buf <= {ex_arstn_buf[0], 1'b1};
  end
end

logic [DIV_WIDTH-1:0] cnt;
logic clk_div;
always_ff @(posedge ex_clk_i or negedge ex_arstn_buffered) begin
  if ( ~ex_arstn_buffered ) begin
    cnt     <= 0;
    clk_div <= 0;
  end else if ( cnt == 0 ) begin
    cnt   <= div_i-1;
    clk_div <= !clk_div;
  end else begin
    cnt   <= cnt - 1;
  end
end

BUFG clkbuf (.O(sys_clk_o),.I(clk_div));

always_ff @(posedge sys_clk_o or negedge ex_arstn_buffered) begin
  if(!ex_arstn_buffered) begin
    sys_rstn_buf <= 2'b0;
  end
  else begin
    sys_rstn_buf <= {sys_rstn_buf[DIV_WIDTH-2:0], 1'b1};
  end
end


endmodule
