//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
// 
// Create Date:    
// Design Name: 
// Module Name:    tb_cybercobra
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: tb for CYBERcobra 3000 Pro 2.1
// 
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

module tb_CYBERcobra();
    
    CYBERcobra dut(
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
    $display( "\nStart test: \n\n===============================================\nAdd CYBERcobra signals to the waveform and then\nCLICK THE BUTTON 'Run All'\n===============================================\n"); $stop();
    rstn = 1'b1;
    #10;
    rstn = 1'b0;
    sw_i = 16'b100001000; //значение, до которого считает счетчик
    //#260;
    //sw_i = 15'b0;
    #10000;
    $display("\n The test is over \n See the internal signals of the CYBERcobra on the waveform \n");
    $finish;
    end
    
endmodule
