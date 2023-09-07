`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
// 
// Create Date:    
// Design Name: 
// Module Name:    tb_riscv_unit
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: tb for datapath
// 
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

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
        #20;
        rst = 0;
        #500;
        $display("\n The test is over \n See the internal signals of the module on the waveform \n");
        $finish;
    end

stall: assert property (
  @(posedge clk)
  disable iff ( rst )
  (top.mem_req) |-> (top.stall) |-> ##1 (!top.stall & top.mem_req)
  
)else $error("\n================================================\nThe realisation of the STALL signal is INCORRECT\n================================================\n");

endmodule
