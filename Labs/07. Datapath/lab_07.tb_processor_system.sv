/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_07_tb_processor_system();

    reg clk;
    reg rst;

    processor_system system(
    .clk_i(clk),
    .rst_i(rst)
    );

  initial clk = 0;
    always #10 clk = ~clk;
    initial begin
      $display( "\nTest has been started.");
      rst = 1;
      #40;
      rst = 0;
      #800;
      $display("\n The test is over \n See the internal signals of the module on the waveform \n");
      $finish;
      #5;
      $display("You're trying to run simulation that has finished. Aborting simulation.")
      $fatal();
  end

stall_seq: assert property (
  @(posedge system.core.clk_i) disable iff ( system.core.rst_i )
    system.core.mem_req_o |-> (system.core.stall_i || $past(system.core.stall_i))
)else $error("\nincorrect implementation of stall signal\n");

stall_seq_fall: assert property (
  @(posedge system.core.clk_i) disable iff ( system.core.rst_i )
    (system.core.stall_i) |=> !system.core.stall_i
)else $error("\nstall must fall exact one cycle after rising\n");
endmodule
