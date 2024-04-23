/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module tb_riscv_unit();

    reg clk;
    reg rst;

    riscv_unit unit(
    .clk_i(clk),
    .rst_i(rst)
    );

    initial clk = 0;
    always #10 clk = ~clk;
    initial begin
        $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
        rst = 1;
        #40;
        rst = 0;
        #800;
        $display("\n The test is over \n See the internal signals of the module on the waveform \n");
        $finish;
    end

stall_seq: assert property (
  @(posedge unit.core.clk_i) disable iff ( unit.core.rst_i )
    unit.core.mem_req_o |-> (unit.core.stall_i || $past(unit.core.stall_i))
)else $error("\nincorrect implementation of stall signal\n");

stall_seq_fall: assert property (
  @(posedge unit.core.clk_i) disable iff ( unit.core.rst_i )
    (unit.core.stall_i) |=> !unit.core.stall_i
)else $error("\nstall must fall exact one cycle after rising\n");
endmodule
