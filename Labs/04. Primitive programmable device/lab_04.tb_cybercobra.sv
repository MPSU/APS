/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_04_tb_CYBERcobra();

  logic [31:0]  OUT;
  logic         clk;
  logic         rst;
  logic [15:0]  sw_i;


  CYBERcobra DUT(
    .clk_i(clk),
    .rst_i(rst),
    .sw_i (sw_i),
    .out_o(OUT)
  );

  initial clk <= 0;
  always #5ns clk = ~clk;

  initial begin
    logic [15:0] count_num;
    $display("Test has been started");
    rst = 1'b1;
    repeat(2)@(posedge clk);
    rst = 1'b0;
    count_num = $urandom_range(5, 10);
    sw_i = count_num;
    repeat(count_num * 2 + 15) begin
      @(posedge clk);
    end
    $display("\nThe test is over.");
    $display("See the internal signals of the CYBERcobra on the waveform");
    $finish;
    @(posedge clk);
    $display("You're trying to run simulation that has finished.");
    $display("Aborting simulation.");
    $fatal();
  end

endmodule
