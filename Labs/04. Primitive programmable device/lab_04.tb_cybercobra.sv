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

    CYBERcobra DUT(
    .clk_i(clk),
    .rst_i(rstn),
    .sw_i (sw_i ),
    .out_o(OUT)
    );

    wire [31:0] OUT;
    reg clk;
    reg rstn;
    reg [15:0] sw_i;

    initial clk <= 0;
    always #5 clk = ~clk;

    initial begin
    $display("Test has been started");
    rstn = 1'b1;
    #10;
    rstn = 1'b0;
    sw_i = 16'b100001000; //значение, до которого считает счетчик
    #10000;
    $display("\n The test is over \n See the internal signals of the CYBERcobra on the waveform \n");
    $finish;
    #5;
    $display("You're trying to run simulation that has finished. Aborting simulation.");
    $fatal();
    end

endmodule
