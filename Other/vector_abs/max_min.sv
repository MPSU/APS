module max_min(
  input  logic [31:0] a,
  input  logic [31:0] b,
  output logic [31:0] max,
  output logic [ 3:0] min
);

  always_comb @(*) begin
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