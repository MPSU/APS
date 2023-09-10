module sys_clk_rst_gen#(
  parameter DIV_WIDTH = 4
)(
    input                   ex_clk_i,
    input                   ex_areset_n_i,
    input  [DIV_WIDTH-1:0]  div_i,

    output                  sys_clk_o,
    output                  sys_reset_o
);

reg [1:0] ex_arstn_buf;
reg [1:0] sys_rstn_buf;

wire ex_arstn_buffered;
assign ex_arstn_buffered = ex_arstn_buf[1];
assign sys_reset_o = !sys_rstn_buf[1];

always @(posedge ex_clk_i or negedge ex_areset_n_i) begin
    if(!ex_areset_n_i) begin
        ex_arstn_buf <= 2'b0;
    end
    else begin
        ex_arstn_buf <= {ex_arstn_buf[0], 1'b1};
    end
end

reg [DIV_WIDTH-1:0] cnt;
reg clk_div;
always@( posedge ex_clk_i or negedge ex_arstn_buffered ) begin
  if ( ~ex_arstn_buffered ) begin
    cnt     <= 0;
    clk_div <= 0;
  end else if ( cnt == 0 ) begin
    cnt   <= div_i;
    clk_div <= !clk_div;
  end else begin
    cnt   <= cnt - 1;
  end
end

BUFG clkbuf (.O(sys_clk_o),.I(clk_div));

always @(posedge sys_clk_o or negedge ex_arstn_buffered) begin
    if(!ex_arstn_buffered) begin
        sys_rstn_buf <= 2'b0;
    end
    else begin
        sys_rstn_buf <= {sys_rstn_buf[0], 1'b1};
    end
end


endmodule
