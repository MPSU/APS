/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module tb_vector_abs();

logic [31:0] a;
logic [31:0] b;
logic [31:0] res;

vector_abs dut(
  .x(a),
  .y(b),
  .abs(res)
);
integer err_count = 0;

task check_result(input logic [31:0]a, b, res);
begin : check_result
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
 check_result(a,b,res);


 a = 1; b = 1;
 #5;
 check_result(a,b,res);

 a = 3; b = 4;
 #5;
 check_result(a,b,res);


 for(i = 0; i < 100; i=i+1) begin
   a = $random()&32'hff; b = $random()&32'hff;
   #5;
   check_result(a,b,res);
 end

 $display("Test has been finished with %d errors", err_count);
 if(err_count == 0) begin
   $display("SUCCESS!");
 end
 $finish();
end
endmodule
