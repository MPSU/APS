/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_11_tb_processor_system();

    reg clk;
    reg rst;

    processor_system system(
    .clk_i(clk),
    .rst_i(rst)
    );

    initial begin
      repeat(1000) begin
        @(posedge clk);
      end
      $fatal(1, "Test has been interrupted by watchdog timer");
    end

    initial clk = 0;
    always #10 clk = ~clk;

    initial begin
        $display( "\nTest has been started");
        system.irq_req = 0;
        rst = 1;
        #40;
        rst = 0;
        repeat(20)@(posedge clk);
        system.irq_req = 1;
        while(system.irq_ret == 0) begin
          @(posedge clk);
        end
        system.irq_req = 0;
        repeat(20)@(posedge clk);
        $display("\n The test is over \n See the internal signals of the module on the waveform \n");
        $finish;
    end

endmodule
