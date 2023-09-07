module tb();

reg [31:0] a;
reg [31:0] b;
wire [31:0] res;

vector_abs dut(
  .x(a),
  .y(b),
  .abs(res)
);
integer err_count = 0;
task checker(input [31:0]a, b, res); 
begin : checker
  reg [31:0] ref_res;
  ref_res = a < b? a/2 + b : a + b/2;
  if (res !== ref_res) begin
    $display("Incorrect res at time %0t:", $time);
    $display("a = %0d, b = %0d", a, b);
    $display("design    res = %0d", res);
    $display("reference res = %0d", ref_res);
    $display("------------------");
    err_count = err_count + 1'b1;
  end
end
endtask

initial begin : test
 integer i;
 $timeformat(-9,0,"ns");
 a = 0; b = 0;
 #5;
 checker(a,b,res);
 
 
 a = 1; b = 1;
 #5;
 checker(a,b,res);

 a = 3; b = 4;
 #5;
 checker(a,b,res);
 
 
 for(i = 0; i < 100; i=i+1) begin
   a = $random()&32'hff; b = $random()&32'hff;
   #5;
   checker(a,b,res);
 end
 
 $display("Test has been finished with %d errors", err_count);
 if(err_count == 0) begin
   $display("SUCCESS!");
 end
 $finish();
end
endmodule