`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
// 
// Create Date:    
// Design Name: 
// Module Name:    tb_data_mem
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: tb for data memory
// 
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

module tb_data_mem();

parameter ADDR_SIZE = 16384;
parameter TIME_OPERATION  = 20;
parameter STEP = 8;

    logic        CLK;
    logic        REQ;
    logic        WE;
    logic [31:0] A;
    logic [31:0] WD;
    logic [31:0] RD;

    data_mem DUT (
    .clk_i          (CLK),
    .mem_req_i      (REQ),
    .write_enable_i (WE ),
    .addr_i         (A  ),
    .write_data_i   (WD),
    .read_data_o    (RD)
    );
    
    logic [31:0] RDa;
    integer i, err_count = 0;
    assign A = i;
    
    parameter CLK_FREQ_MHz   = 100;
    parameter CLK_SEMI_PERIOD= 1e3/CLK_FREQ_MHz/2;

    initial CLK <= 0;
    always #CLK_SEMI_PERIOD CLK = ~CLK;

    initial begin
        $timeformat(-9, 2, " ns", 3);
        $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
        REQ = 1;
        WE = 0;
        i = 0; #10;
        if (RD !== 32'hx) begin
            $display("The data memory should not be initialized by the $readmemh function");
            err_count = err_count + 1;
        end
        for (i = 0; i < ADDR_SIZE; i = i + 4) begin
            @(posedge CLK);
            WE = 1;
            WD = $urandom;
        end
        for (i = 0; i < (ADDR_SIZE+STEP); i = i + 1 + $urandom() % STEP) begin
            if (i < (ADDR_SIZE)) begin
                REQ = |($urandom %10);
                WE = 0;
                #TIME_OPERATION;
                RDa = RD;
                WD = $urandom;
                #TIME_OPERATION;
                WE = $urandom % 2;
                #TIME_OPERATION;
                if ((WE && REQ || !REQ) && RD !== 32'd4195425967) begin
                    $display("When writing (write_enable_i = %h) read_data_o should be equal to fa11_1eaf, your data: %h_%h, time: %t", WE, RD[31:16],RD[15:0], $time);
                    err_count = err_count + 1;
                end
                if ((!WE && REQ) && RD !== RDa) begin
                    $display("When reading (write_enable_i = %h), the data %h is overwritten with data %h at address %h, time: %t", WE, RDa, RD, A, $time);
                    err_count = err_count + 1;
                end
            end
            else begin
                WE = 0;
                REQ = 1;
                #TIME_OPERATION;
                if (RD !== 32'd3735928559) begin
                    $display("When reading (write_enable_i = %h) at address greater than 16383 (current addr = %d), it should return dead_beef, but your data: %h_%h, time: %t", WE, A, RD[31:16],RD[15:0], $time);
                    err_count = err_count + 1;
                end
            end
            #TIME_OPERATION;
        end
        #TIME_OPERATION;
        REQ = 1;
        WE = 0;
        #TIME_OPERATION;
        for (i = 0; i < 4; i = i + 1) begin 
          if(i==0) begin 
            repeat(2)@(posedge CLK); 
            #1; RDa = RD;
          end else
          if(RD !== RDa) begin
            $display("incorrect conversion of the reading address = %h, time: %t", A, $time);
            err_count = err_count + 1;
          end
          #TIME_OPERATION;
        end
        i = 0; WE = 0; REQ = 1;
        @(posedge CLK);
        @(negedge CLK);
        i = 4;
        #1; RDa = RD;
        @(posedge CLK); #1;
        if (RD == RDa) begin
            $display("reading from data memory must be synchronous, time: %t", $time);
            err_count = err_count + 1;
        end
        @(posedge CLK);
        i = {14{1'b1}};
        repeat(2) @(posedge CLK);
        if (RD === 'd3735928559) begin
            $display("incorrect reading from address = %d, data = %h", A, RD);
            err_count = err_count + 1;
        end
        $display("Number of errors: %d", err_count);
        if( !err_count )  $display("\ndata_mem SUCCESS!!!\n");
        $finish();
    end
endmodule
