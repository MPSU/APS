`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
// 
// Create Date:    
// Design Name: 
// Module Name:    tb_fulladder
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: tb for 1-bit fulladder
// 
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

module tb_fulladder();

parameter TIME_OPERATION  = 100;
parameter TEST_VALUES = 8;

    wire tb_a_i;
    wire tb_b_i;
    wire tb_carry_i;
    wire tb_carry_o;
    wire tb_sum_o;


    fulladder DUT (
        .a_i(tb_a_i),
        .b_i(tb_b_i),
        .sum_o(tb_sum_o),
        .carry_i(tb_carry_i),
        .carry_o(tb_carry_o)
    );

    integer     i, err_count = 0;
    reg [4:0] running_line;
    reg [5*8-1:0] line_dump;
    wire sum_dump;
    wire carry_o_dump;

    assign tb_a_i = running_line[4];
    assign tb_b_i = running_line[3];
    assign tb_carry_i = running_line[2];
    assign sum_dump = running_line[1];
    assign carry_o_dump = running_line[0];

    initial begin
        $display( "Start test: ");
        for ( i = 0; i < TEST_VALUES; i = i + 1 )
            begin
                running_line = line_dump[i*5+:5];
                #TIME_OPERATION;
                if( (tb_carry_o !== carry_o_dump) || (tb_sum_o !== sum_dump) ) begin
                    $display("ERROR! carry_i = %b; (a)%b + (b)%b = ", tb_carry_i, tb_a_i, tb_b_i, "(carry_o)%b (sum_o)%b;", tb_carry_o, tb_sum_o, " carry_o_dump: %b, sum_dump: %b", carry_o_dump, sum_dump);
                    err_count = err_count + 1'b1;
                end
            end
        $display("Number of errors: %d", err_count);
        if( !err_count )  $display("\nfulladder SUCCESS!!!\n");
        $finish();
    end

    initial line_dump = {
    5'b00000,
    5'b10010,
    5'b01010,
    5'b11001,
    5'b00110,
    5'b10101,
    5'b01101,
    5'b11111};

endmodule
