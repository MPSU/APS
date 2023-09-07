module max_min(
  input [31:0] a,
  input [31:0] b,
  output reg[31:0] max,
  output reg[ 3:0] min
);

  always @(*) begin
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