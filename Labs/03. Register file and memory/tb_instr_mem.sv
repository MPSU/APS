`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
// 
// Create Date:    
// Design Name: 
// Module Name:    tb_instr_mem
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions: 
// Description: tb for instruction memory
// 
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////

module tb_instr_mem();

parameter ADDR_SIZE = 1021;
parameter TIME_OPERATION  = 100;
    
    wire [31:0] A;
    wire [31:0] RD;
    wire [31:0] RDref;
        
    instr_mem_ref8 DUTref(
    .A(A),
    .RD(RDref)
    );
    
    instr_mem DUT (
    .addr_i(A),
    .read_data_o(RD)
    );
    
    integer i, err_count = 0;
    
    assign A = i;
    
    initial begin
        $timeformat (-9, 2, "ns");
        $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
        for (i = 0; i < ADDR_SIZE; i = i + 1) begin
            #TIME_OPERATION;
            if ( RD !== RDref) begin
                $display("time = %0t, address %h. Invalid data %h, correct data %h", $time, A, RD, RDref);
                err_count = err_count + 1;
            end
        end
        for (i = 1021; i < 1024; i = i + 1) begin
            #TIME_OPERATION;
            if ( RD !== 32'b0) begin
                $display("time = %0t, ERROR! Addr = %d", $time, A, " %h != 0", RD);
                err_count = err_count + 1;
            end
        end
        $display("Number of errors: %d", err_count);
        if( !err_count )  $display("\n instr_mem SUCCESS!!!\n");
        $finish();
    end
    
endmodule


(* STRUCTURAL_NETLIST = "yes" *)
module instr_mem_ref8
   (A,
    RD);
  input [31:0]A;
  output [31:0]RD;

  wire [31:0]A;
  wire [9:0]A_IBUF;
  wire [31:0]RD;
  wire [31:0]RD_OBUF;
  wire \RD_OBUF[0]_inst_i_10_n_0 ;
  wire \RD_OBUF[0]_inst_i_11_n_0 ;
  wire \RD_OBUF[0]_inst_i_12_n_0 ;
  wire \RD_OBUF[0]_inst_i_13_n_0 ;
  wire \RD_OBUF[0]_inst_i_2_n_0 ;
  wire \RD_OBUF[0]_inst_i_3_n_0 ;
  wire \RD_OBUF[0]_inst_i_4_n_0 ;
  wire \RD_OBUF[0]_inst_i_5_n_0 ;
  wire \RD_OBUF[0]_inst_i_6_n_0 ;
  wire \RD_OBUF[0]_inst_i_7_n_0 ;
  wire \RD_OBUF[0]_inst_i_8_n_0 ;
  wire \RD_OBUF[0]_inst_i_9_n_0 ;
  wire \RD_OBUF[10]_inst_i_10_n_0 ;
  wire \RD_OBUF[10]_inst_i_11_n_0 ;
  wire \RD_OBUF[10]_inst_i_2_n_0 ;
  wire \RD_OBUF[10]_inst_i_3_n_0 ;
  wire \RD_OBUF[10]_inst_i_4_n_0 ;
  wire \RD_OBUF[10]_inst_i_5_n_0 ;
  wire \RD_OBUF[10]_inst_i_6_n_0 ;
  wire \RD_OBUF[10]_inst_i_7_n_0 ;
  wire \RD_OBUF[10]_inst_i_8_n_0 ;
  wire \RD_OBUF[10]_inst_i_9_n_0 ;
  wire \RD_OBUF[11]_inst_i_10_n_0 ;
  wire \RD_OBUF[11]_inst_i_11_n_0 ;
  wire \RD_OBUF[11]_inst_i_2_n_0 ;
  wire \RD_OBUF[11]_inst_i_3_n_0 ;
  wire \RD_OBUF[11]_inst_i_4_n_0 ;
  wire \RD_OBUF[11]_inst_i_5_n_0 ;
  wire \RD_OBUF[11]_inst_i_6_n_0 ;
  wire \RD_OBUF[11]_inst_i_7_n_0 ;
  wire \RD_OBUF[11]_inst_i_8_n_0 ;
  wire \RD_OBUF[11]_inst_i_9_n_0 ;
  wire \RD_OBUF[12]_inst_i_10_n_0 ;
  wire \RD_OBUF[12]_inst_i_11_n_0 ;
  wire \RD_OBUF[12]_inst_i_2_n_0 ;
  wire \RD_OBUF[12]_inst_i_3_n_0 ;
  wire \RD_OBUF[12]_inst_i_4_n_0 ;
  wire \RD_OBUF[12]_inst_i_5_n_0 ;
  wire \RD_OBUF[12]_inst_i_6_n_0 ;
  wire \RD_OBUF[12]_inst_i_7_n_0 ;
  wire \RD_OBUF[12]_inst_i_8_n_0 ;
  wire \RD_OBUF[12]_inst_i_9_n_0 ;
  wire \RD_OBUF[13]_inst_i_2_n_0 ;
  wire \RD_OBUF[13]_inst_i_3_n_0 ;
  wire \RD_OBUF[13]_inst_i_4_n_0 ;
  wire \RD_OBUF[13]_inst_i_5_n_0 ;
  wire \RD_OBUF[13]_inst_i_6_n_0 ;
  wire \RD_OBUF[13]_inst_i_7_n_0 ;
  wire \RD_OBUF[13]_inst_i_8_n_0 ;
  wire \RD_OBUF[14]_inst_i_10_n_0 ;
  wire \RD_OBUF[14]_inst_i_11_n_0 ;
  wire \RD_OBUF[14]_inst_i_2_n_0 ;
  wire \RD_OBUF[14]_inst_i_3_n_0 ;
  wire \RD_OBUF[14]_inst_i_4_n_0 ;
  wire \RD_OBUF[14]_inst_i_5_n_0 ;
  wire \RD_OBUF[14]_inst_i_6_n_0 ;
  wire \RD_OBUF[14]_inst_i_7_n_0 ;
  wire \RD_OBUF[14]_inst_i_8_n_0 ;
  wire \RD_OBUF[14]_inst_i_9_n_0 ;
  wire \RD_OBUF[15]_inst_i_10_n_0 ;
  wire \RD_OBUF[15]_inst_i_11_n_0 ;
  wire \RD_OBUF[15]_inst_i_12_n_0 ;
  wire \RD_OBUF[15]_inst_i_13_n_0 ;
  wire \RD_OBUF[15]_inst_i_2_n_0 ;
  wire \RD_OBUF[15]_inst_i_3_n_0 ;
  wire \RD_OBUF[15]_inst_i_4_n_0 ;
  wire \RD_OBUF[15]_inst_i_5_n_0 ;
  wire \RD_OBUF[15]_inst_i_6_n_0 ;
  wire \RD_OBUF[15]_inst_i_7_n_0 ;
  wire \RD_OBUF[15]_inst_i_8_n_0 ;
  wire \RD_OBUF[15]_inst_i_9_n_0 ;
  wire \RD_OBUF[16]_inst_i_10_n_0 ;
  wire \RD_OBUF[16]_inst_i_11_n_0 ;
  wire \RD_OBUF[16]_inst_i_2_n_0 ;
  wire \RD_OBUF[16]_inst_i_3_n_0 ;
  wire \RD_OBUF[16]_inst_i_4_n_0 ;
  wire \RD_OBUF[16]_inst_i_5_n_0 ;
  wire \RD_OBUF[16]_inst_i_6_n_0 ;
  wire \RD_OBUF[16]_inst_i_7_n_0 ;
  wire \RD_OBUF[16]_inst_i_8_n_0 ;
  wire \RD_OBUF[16]_inst_i_9_n_0 ;
  wire \RD_OBUF[17]_inst_i_10_n_0 ;
  wire \RD_OBUF[17]_inst_i_11_n_0 ;
  wire \RD_OBUF[17]_inst_i_2_n_0 ;
  wire \RD_OBUF[17]_inst_i_3_n_0 ;
  wire \RD_OBUF[17]_inst_i_4_n_0 ;
  wire \RD_OBUF[17]_inst_i_5_n_0 ;
  wire \RD_OBUF[17]_inst_i_6_n_0 ;
  wire \RD_OBUF[17]_inst_i_7_n_0 ;
  wire \RD_OBUF[17]_inst_i_8_n_0 ;
  wire \RD_OBUF[17]_inst_i_9_n_0 ;
  wire \RD_OBUF[18]_inst_i_10_n_0 ;
  wire \RD_OBUF[18]_inst_i_11_n_0 ;
  wire \RD_OBUF[18]_inst_i_2_n_0 ;
  wire \RD_OBUF[18]_inst_i_3_n_0 ;
  wire \RD_OBUF[18]_inst_i_4_n_0 ;
  wire \RD_OBUF[18]_inst_i_5_n_0 ;
  wire \RD_OBUF[18]_inst_i_6_n_0 ;
  wire \RD_OBUF[18]_inst_i_7_n_0 ;
  wire \RD_OBUF[18]_inst_i_8_n_0 ;
  wire \RD_OBUF[18]_inst_i_9_n_0 ;
  wire \RD_OBUF[19]_inst_i_10_n_0 ;
  wire \RD_OBUF[19]_inst_i_11_n_0 ;
  wire \RD_OBUF[19]_inst_i_2_n_0 ;
  wire \RD_OBUF[19]_inst_i_3_n_0 ;
  wire \RD_OBUF[19]_inst_i_4_n_0 ;
  wire \RD_OBUF[19]_inst_i_5_n_0 ;
  wire \RD_OBUF[19]_inst_i_6_n_0 ;
  wire \RD_OBUF[19]_inst_i_7_n_0 ;
  wire \RD_OBUF[19]_inst_i_8_n_0 ;
  wire \RD_OBUF[19]_inst_i_9_n_0 ;
  wire \RD_OBUF[1]_inst_i_10_n_0 ;
  wire \RD_OBUF[1]_inst_i_11_n_0 ;
  wire \RD_OBUF[1]_inst_i_12_n_0 ;
  wire \RD_OBUF[1]_inst_i_13_n_0 ;
  wire \RD_OBUF[1]_inst_i_2_n_0 ;
  wire \RD_OBUF[1]_inst_i_3_n_0 ;
  wire \RD_OBUF[1]_inst_i_4_n_0 ;
  wire \RD_OBUF[1]_inst_i_5_n_0 ;
  wire \RD_OBUF[1]_inst_i_6_n_0 ;
  wire \RD_OBUF[1]_inst_i_7_n_0 ;
  wire \RD_OBUF[1]_inst_i_8_n_0 ;
  wire \RD_OBUF[1]_inst_i_9_n_0 ;
  wire \RD_OBUF[20]_inst_i_10_n_0 ;
  wire \RD_OBUF[20]_inst_i_11_n_0 ;
  wire \RD_OBUF[20]_inst_i_2_n_0 ;
  wire \RD_OBUF[20]_inst_i_3_n_0 ;
  wire \RD_OBUF[20]_inst_i_4_n_0 ;
  wire \RD_OBUF[20]_inst_i_5_n_0 ;
  wire \RD_OBUF[20]_inst_i_6_n_0 ;
  wire \RD_OBUF[20]_inst_i_7_n_0 ;
  wire \RD_OBUF[20]_inst_i_8_n_0 ;
  wire \RD_OBUF[20]_inst_i_9_n_0 ;
  wire \RD_OBUF[21]_inst_i_2_n_0 ;
  wire \RD_OBUF[21]_inst_i_3_n_0 ;
  wire \RD_OBUF[21]_inst_i_4_n_0 ;
  wire \RD_OBUF[21]_inst_i_5_n_0 ;
  wire \RD_OBUF[21]_inst_i_6_n_0 ;
  wire \RD_OBUF[21]_inst_i_7_n_0 ;
  wire \RD_OBUF[21]_inst_i_8_n_0 ;
  wire \RD_OBUF[22]_inst_i_10_n_0 ;
  wire \RD_OBUF[22]_inst_i_11_n_0 ;
  wire \RD_OBUF[22]_inst_i_2_n_0 ;
  wire \RD_OBUF[22]_inst_i_3_n_0 ;
  wire \RD_OBUF[22]_inst_i_4_n_0 ;
  wire \RD_OBUF[22]_inst_i_5_n_0 ;
  wire \RD_OBUF[22]_inst_i_6_n_0 ;
  wire \RD_OBUF[22]_inst_i_7_n_0 ;
  wire \RD_OBUF[22]_inst_i_8_n_0 ;
  wire \RD_OBUF[22]_inst_i_9_n_0 ;
  wire \RD_OBUF[23]_inst_i_10_n_0 ;
  wire \RD_OBUF[23]_inst_i_11_n_0 ;
  wire \RD_OBUF[23]_inst_i_12_n_0 ;
  wire \RD_OBUF[23]_inst_i_13_n_0 ;
  wire \RD_OBUF[23]_inst_i_2_n_0 ;
  wire \RD_OBUF[23]_inst_i_3_n_0 ;
  wire \RD_OBUF[23]_inst_i_4_n_0 ;
  wire \RD_OBUF[23]_inst_i_5_n_0 ;
  wire \RD_OBUF[23]_inst_i_6_n_0 ;
  wire \RD_OBUF[23]_inst_i_7_n_0 ;
  wire \RD_OBUF[23]_inst_i_8_n_0 ;
  wire \RD_OBUF[23]_inst_i_9_n_0 ;
  wire \RD_OBUF[24]_inst_i_10_n_0 ;
  wire \RD_OBUF[24]_inst_i_11_n_0 ;
  wire \RD_OBUF[24]_inst_i_2_n_0 ;
  wire \RD_OBUF[24]_inst_i_3_n_0 ;
  wire \RD_OBUF[24]_inst_i_4_n_0 ;
  wire \RD_OBUF[24]_inst_i_5_n_0 ;
  wire \RD_OBUF[24]_inst_i_6_n_0 ;
  wire \RD_OBUF[24]_inst_i_7_n_0 ;
  wire \RD_OBUF[24]_inst_i_8_n_0 ;
  wire \RD_OBUF[24]_inst_i_9_n_0 ;
  wire \RD_OBUF[25]_inst_i_10_n_0 ;
  wire \RD_OBUF[25]_inst_i_11_n_0 ;
  wire \RD_OBUF[25]_inst_i_2_n_0 ;
  wire \RD_OBUF[25]_inst_i_3_n_0 ;
  wire \RD_OBUF[25]_inst_i_4_n_0 ;
  wire \RD_OBUF[25]_inst_i_5_n_0 ;
  wire \RD_OBUF[25]_inst_i_6_n_0 ;
  wire \RD_OBUF[25]_inst_i_7_n_0 ;
  wire \RD_OBUF[25]_inst_i_8_n_0 ;
  wire \RD_OBUF[25]_inst_i_9_n_0 ;
  wire \RD_OBUF[26]_inst_i_10_n_0 ;
  wire \RD_OBUF[26]_inst_i_11_n_0 ;
  wire \RD_OBUF[26]_inst_i_2_n_0 ;
  wire \RD_OBUF[26]_inst_i_3_n_0 ;
  wire \RD_OBUF[26]_inst_i_4_n_0 ;
  wire \RD_OBUF[26]_inst_i_5_n_0 ;
  wire \RD_OBUF[26]_inst_i_6_n_0 ;
  wire \RD_OBUF[26]_inst_i_7_n_0 ;
  wire \RD_OBUF[26]_inst_i_8_n_0 ;
  wire \RD_OBUF[26]_inst_i_9_n_0 ;
  wire \RD_OBUF[27]_inst_i_10_n_0 ;
  wire \RD_OBUF[27]_inst_i_11_n_0 ;
  wire \RD_OBUF[27]_inst_i_2_n_0 ;
  wire \RD_OBUF[27]_inst_i_3_n_0 ;
  wire \RD_OBUF[27]_inst_i_4_n_0 ;
  wire \RD_OBUF[27]_inst_i_5_n_0 ;
  wire \RD_OBUF[27]_inst_i_6_n_0 ;
  wire \RD_OBUF[27]_inst_i_7_n_0 ;
  wire \RD_OBUF[27]_inst_i_8_n_0 ;
  wire \RD_OBUF[27]_inst_i_9_n_0 ;
  wire \RD_OBUF[28]_inst_i_10_n_0 ;
  wire \RD_OBUF[28]_inst_i_11_n_0 ;
  wire \RD_OBUF[28]_inst_i_2_n_0 ;
  wire \RD_OBUF[28]_inst_i_3_n_0 ;
  wire \RD_OBUF[28]_inst_i_4_n_0 ;
  wire \RD_OBUF[28]_inst_i_5_n_0 ;
  wire \RD_OBUF[28]_inst_i_6_n_0 ;
  wire \RD_OBUF[28]_inst_i_7_n_0 ;
  wire \RD_OBUF[28]_inst_i_8_n_0 ;
  wire \RD_OBUF[28]_inst_i_9_n_0 ;
  wire \RD_OBUF[29]_inst_i_2_n_0 ;
  wire \RD_OBUF[29]_inst_i_3_n_0 ;
  wire \RD_OBUF[29]_inst_i_5_n_0 ;
  wire \RD_OBUF[29]_inst_i_7_n_0 ;
  wire \RD_OBUF[2]_inst_i_10_n_0 ;
  wire \RD_OBUF[2]_inst_i_11_n_0 ;
  wire \RD_OBUF[2]_inst_i_12_n_0 ;
  wire \RD_OBUF[2]_inst_i_13_n_0 ;
  wire \RD_OBUF[2]_inst_i_2_n_0 ;
  wire \RD_OBUF[2]_inst_i_3_n_0 ;
  wire \RD_OBUF[2]_inst_i_4_n_0 ;
  wire \RD_OBUF[2]_inst_i_5_n_0 ;
  wire \RD_OBUF[2]_inst_i_6_n_0 ;
  wire \RD_OBUF[2]_inst_i_7_n_0 ;
  wire \RD_OBUF[2]_inst_i_8_n_0 ;
  wire \RD_OBUF[2]_inst_i_9_n_0 ;
  wire \RD_OBUF[30]_inst_i_10_n_0 ;
  wire \RD_OBUF[30]_inst_i_11_n_0 ;
  wire \RD_OBUF[30]_inst_i_2_n_0 ;
  wire \RD_OBUF[30]_inst_i_3_n_0 ;
  wire \RD_OBUF[30]_inst_i_4_n_0 ;
  wire \RD_OBUF[30]_inst_i_5_n_0 ;
  wire \RD_OBUF[30]_inst_i_6_n_0 ;
  wire \RD_OBUF[30]_inst_i_7_n_0 ;
  wire \RD_OBUF[30]_inst_i_8_n_0 ;
  wire \RD_OBUF[30]_inst_i_9_n_0 ;
  wire \RD_OBUF[31]_inst_i_10_n_0 ;
  wire \RD_OBUF[31]_inst_i_11_n_0 ;
  wire \RD_OBUF[31]_inst_i_12_n_0 ;
  wire \RD_OBUF[31]_inst_i_13_n_0 ;
  wire \RD_OBUF[31]_inst_i_3_n_0 ;
  wire \RD_OBUF[31]_inst_i_4_n_0 ;
  wire \RD_OBUF[31]_inst_i_5_n_0 ;
  wire \RD_OBUF[31]_inst_i_6_n_0 ;
  wire \RD_OBUF[31]_inst_i_7_n_0 ;
  wire \RD_OBUF[31]_inst_i_8_n_0 ;
  wire \RD_OBUF[31]_inst_i_9_n_0 ;
  wire \RD_OBUF[3]_inst_i_10_n_0 ;
  wire \RD_OBUF[3]_inst_i_11_n_0 ;
  wire \RD_OBUF[3]_inst_i_12_n_0 ;
  wire \RD_OBUF[3]_inst_i_13_n_0 ;
  wire \RD_OBUF[3]_inst_i_2_n_0 ;
  wire \RD_OBUF[3]_inst_i_3_n_0 ;
  wire \RD_OBUF[3]_inst_i_4_n_0 ;
  wire \RD_OBUF[3]_inst_i_5_n_0 ;
  wire \RD_OBUF[3]_inst_i_6_n_0 ;
  wire \RD_OBUF[3]_inst_i_7_n_0 ;
  wire \RD_OBUF[3]_inst_i_8_n_0 ;
  wire \RD_OBUF[3]_inst_i_9_n_0 ;
  wire \RD_OBUF[4]_inst_i_10_n_0 ;
  wire \RD_OBUF[4]_inst_i_11_n_0 ;
  wire \RD_OBUF[4]_inst_i_12_n_0 ;
  wire \RD_OBUF[4]_inst_i_13_n_0 ;
  wire \RD_OBUF[4]_inst_i_2_n_0 ;
  wire \RD_OBUF[4]_inst_i_3_n_0 ;
  wire \RD_OBUF[4]_inst_i_4_n_0 ;
  wire \RD_OBUF[4]_inst_i_5_n_0 ;
  wire \RD_OBUF[4]_inst_i_6_n_0 ;
  wire \RD_OBUF[4]_inst_i_7_n_0 ;
  wire \RD_OBUF[4]_inst_i_8_n_0 ;
  wire \RD_OBUF[4]_inst_i_9_n_0 ;
  wire \RD_OBUF[5]_inst_i_2_n_0 ;
  wire \RD_OBUF[5]_inst_i_3_n_0 ;
  wire \RD_OBUF[5]_inst_i_4_n_0 ;
  wire \RD_OBUF[5]_inst_i_5_n_0 ;
  wire \RD_OBUF[6]_inst_i_10_n_0 ;
  wire \RD_OBUF[6]_inst_i_11_n_0 ;
  wire \RD_OBUF[6]_inst_i_12_n_0 ;
  wire \RD_OBUF[6]_inst_i_13_n_0 ;
  wire \RD_OBUF[6]_inst_i_2_n_0 ;
  wire \RD_OBUF[6]_inst_i_3_n_0 ;
  wire \RD_OBUF[6]_inst_i_4_n_0 ;
  wire \RD_OBUF[6]_inst_i_5_n_0 ;
  wire \RD_OBUF[6]_inst_i_6_n_0 ;
  wire \RD_OBUF[6]_inst_i_7_n_0 ;
  wire \RD_OBUF[6]_inst_i_8_n_0 ;
  wire \RD_OBUF[6]_inst_i_9_n_0 ;
  wire \RD_OBUF[7]_inst_i_10_n_0 ;
  wire \RD_OBUF[7]_inst_i_11_n_0 ;
  wire \RD_OBUF[7]_inst_i_12_n_0 ;
  wire \RD_OBUF[7]_inst_i_13_n_0 ;
  wire \RD_OBUF[7]_inst_i_2_n_0 ;
  wire \RD_OBUF[7]_inst_i_3_n_0 ;
  wire \RD_OBUF[7]_inst_i_4_n_0 ;
  wire \RD_OBUF[7]_inst_i_5_n_0 ;
  wire \RD_OBUF[7]_inst_i_6_n_0 ;
  wire \RD_OBUF[7]_inst_i_7_n_0 ;
  wire \RD_OBUF[7]_inst_i_8_n_0 ;
  wire \RD_OBUF[7]_inst_i_9_n_0 ;
  wire \RD_OBUF[8]_inst_i_10_n_0 ;
  wire \RD_OBUF[8]_inst_i_11_n_0 ;
  wire \RD_OBUF[8]_inst_i_2_n_0 ;
  wire \RD_OBUF[8]_inst_i_3_n_0 ;
  wire \RD_OBUF[8]_inst_i_4_n_0 ;
  wire \RD_OBUF[8]_inst_i_5_n_0 ;
  wire \RD_OBUF[8]_inst_i_6_n_0 ;
  wire \RD_OBUF[8]_inst_i_7_n_0 ;
  wire \RD_OBUF[8]_inst_i_8_n_0 ;
  wire \RD_OBUF[8]_inst_i_9_n_0 ;
  wire \RD_OBUF[9]_inst_i_10_n_0 ;
  wire \RD_OBUF[9]_inst_i_11_n_0 ;
  wire \RD_OBUF[9]_inst_i_2_n_0 ;
  wire \RD_OBUF[9]_inst_i_3_n_0 ;
  wire \RD_OBUF[9]_inst_i_4_n_0 ;
  wire \RD_OBUF[9]_inst_i_5_n_0 ;
  wire \RD_OBUF[9]_inst_i_6_n_0 ;
  wire \RD_OBUF[9]_inst_i_7_n_0 ;
  wire \RD_OBUF[9]_inst_i_8_n_0 ;
  wire \RD_OBUF[9]_inst_i_9_n_0 ;
  wire g0_b0__0_n_0;
  wire g0_b0__1_n_0;
  wire g0_b0__2_n_0;
  wire g0_b0_n_0;
  wire g0_b1__0_n_0;
  wire g0_b1__1_n_0;
  wire g0_b1__2_n_0;
  wire g0_b1_n_0;
  wire g0_b2__0_n_0;
  wire g0_b2__1_n_0;
  wire g0_b2__2_n_0;
  wire g0_b2_n_0;
  wire g0_b3__0_n_0;
  wire g0_b3__1_n_0;
  wire g0_b3__2_n_0;
  wire g0_b3_n_0;
  wire g0_b4__0_n_0;
  wire g0_b4__1_n_0;
  wire g0_b4__2_n_0;
  wire g0_b4_n_0;
  wire g0_b5__0_n_0;
  wire g0_b5__1_n_0;
  wire g0_b5__2_n_0;
  wire g0_b5_n_0;
  wire g0_b6__0_n_0;
  wire g0_b6__1_n_0;
  wire g0_b6__2_n_0;
  wire g0_b6_n_0;
  wire g0_b7__0_n_0;
  wire g0_b7__1_n_0;
  wire g0_b7__2_n_0;
  wire g0_b7_n_0;
  wire g10_b0__0_n_0;
  wire g10_b0__1_n_0;
  wire g10_b0__2_n_0;
  wire g10_b0_n_0;
  wire g10_b1__0_n_0;
  wire g10_b1__1_n_0;
  wire g10_b1__2_n_0;
  wire g10_b1_n_0;
  wire g10_b2__0_n_0;
  wire g10_b2__1_n_0;
  wire g10_b2__2_n_0;
  wire g10_b2_n_0;
  wire g10_b3__0_n_0;
  wire g10_b3__1_n_0;
  wire g10_b3__2_n_0;
  wire g10_b3_n_0;
  wire g10_b4__0_n_0;
  wire g10_b4__1_n_0;
  wire g10_b4__2_n_0;
  wire g10_b4_n_0;
  wire g10_b6__0_n_0;
  wire g10_b6__1_n_0;
  wire g10_b6__2_n_0;
  wire g10_b6_n_0;
  wire g10_b7__0_n_0;
  wire g10_b7__1_n_0;
  wire g10_b7__2_n_0;
  wire g10_b7_n_0;
  wire g11_b0__0_n_0;
  wire g11_b0__1_n_0;
  wire g11_b0__2_n_0;
  wire g11_b0_n_0;
  wire g11_b1__0_n_0;
  wire g11_b1__1_n_0;
  wire g11_b1__2_n_0;
  wire g11_b1_n_0;
  wire g11_b2__0_n_0;
  wire g11_b2__1_n_0;
  wire g11_b2__2_n_0;
  wire g11_b2_n_0;
  wire g11_b3__0_n_0;
  wire g11_b3__1_n_0;
  wire g11_b3__2_n_0;
  wire g11_b3_n_0;
  wire g11_b4__0_n_0;
  wire g11_b4__1_n_0;
  wire g11_b4__2_n_0;
  wire g11_b4_n_0;
  wire g11_b6__0_n_0;
  wire g11_b6__1_n_0;
  wire g11_b6__2_n_0;
  wire g11_b6_n_0;
  wire g11_b7__0_n_0;
  wire g11_b7__1_n_0;
  wire g11_b7__2_n_0;
  wire g11_b7_n_0;
  wire g12_b0__0_n_0;
  wire g12_b0__1_n_0;
  wire g12_b0__2_n_0;
  wire g12_b0_n_0;
  wire g12_b1__0_n_0;
  wire g12_b1__1_n_0;
  wire g12_b1__2_n_0;
  wire g12_b1_n_0;
  wire g12_b2__0_n_0;
  wire g12_b2__1_n_0;
  wire g12_b2__2_n_0;
  wire g12_b2_n_0;
  wire g12_b3__0_n_0;
  wire g12_b3__1_n_0;
  wire g12_b3__2_n_0;
  wire g12_b3_n_0;
  wire g12_b4__0_n_0;
  wire g12_b4__1_n_0;
  wire g12_b4__2_n_0;
  wire g12_b4_n_0;
  wire g12_b6__0_n_0;
  wire g12_b6__1_n_0;
  wire g12_b6__2_n_0;
  wire g12_b6_n_0;
  wire g12_b7__0_n_0;
  wire g12_b7__1_n_0;
  wire g12_b7__2_n_0;
  wire g12_b7_n_0;
  wire g13_b0__0_n_0;
  wire g13_b0__1_n_0;
  wire g13_b0__2_n_0;
  wire g13_b0_n_0;
  wire g13_b1__0_n_0;
  wire g13_b1__1_n_0;
  wire g13_b1__2_n_0;
  wire g13_b1_n_0;
  wire g13_b2__0_n_0;
  wire g13_b2__1_n_0;
  wire g13_b2__2_n_0;
  wire g13_b2_n_0;
  wire g13_b3__0_n_0;
  wire g13_b3__1_n_0;
  wire g13_b3__2_n_0;
  wire g13_b3_n_0;
  wire g13_b4__0_n_0;
  wire g13_b4__1_n_0;
  wire g13_b4__2_n_0;
  wire g13_b4_n_0;
  wire g13_b6__0_n_0;
  wire g13_b6__1_n_0;
  wire g13_b6__2_n_0;
  wire g13_b6_n_0;
  wire g13_b7__0_n_0;
  wire g13_b7__1_n_0;
  wire g13_b7__2_n_0;
  wire g13_b7_n_0;
  wire g14_b0__0_n_0;
  wire g14_b0__1_n_0;
  wire g14_b0__2_n_0;
  wire g14_b0_n_0;
  wire g14_b1__0_n_0;
  wire g14_b1__1_n_0;
  wire g14_b1__2_n_0;
  wire g14_b1_n_0;
  wire g14_b2__0_n_0;
  wire g14_b2__1_n_0;
  wire g14_b2__2_n_0;
  wire g14_b2_n_0;
  wire g14_b3__0_n_0;
  wire g14_b3__1_n_0;
  wire g14_b3__2_n_0;
  wire g14_b3_n_0;
  wire g14_b4__0_n_0;
  wire g14_b4__1_n_0;
  wire g14_b4__2_n_0;
  wire g14_b4_n_0;
  wire g14_b6__0_n_0;
  wire g14_b6__1_n_0;
  wire g14_b6__2_n_0;
  wire g14_b6_n_0;
  wire g14_b7__0_n_0;
  wire g14_b7__1_n_0;
  wire g14_b7__2_n_0;
  wire g14_b7_n_0;
  wire g15_b0__0_n_0;
  wire g15_b0__1_n_0;
  wire g15_b0__2_n_0;
  wire g15_b0_n_0;
  wire g15_b1__0_n_0;
  wire g15_b1__1_n_0;
  wire g15_b1__2_n_0;
  wire g15_b1_n_0;
  wire g15_b2__0_n_0;
  wire g15_b2__1_n_0;
  wire g15_b2__2_n_0;
  wire g15_b2_n_0;
  wire g15_b3__0_n_0;
  wire g15_b3__1_n_0;
  wire g15_b3__2_n_0;
  wire g15_b3_n_0;
  wire g15_b4__0_n_0;
  wire g15_b4__1_n_0;
  wire g15_b4__2_n_0;
  wire g15_b4_n_0;
  wire g15_b6__0_n_0;
  wire g15_b6__1_n_0;
  wire g15_b6__2_n_0;
  wire g15_b6_n_0;
  wire g15_b7__0_n_0;
  wire g15_b7__1_n_0;
  wire g15_b7__2_n_0;
  wire g15_b7_i_1__0_n_0;
  wire g15_b7_i_1__1_n_0;
  wire g15_b7_i_2__0_n_0;
  wire g15_b7_i_2_n_0;
  wire g15_b7_i_3_n_0;
  wire g15_b7_i_4_n_0;
  wire g15_b7_i_5_n_0;
  wire g15_b7_n_0;
  wire g1_b0__0_n_0;
  wire g1_b0__1_n_0;
  wire g1_b0__2_n_0;
  wire g1_b0_n_0;
  wire g1_b1__0_n_0;
  wire g1_b1__1_n_0;
  wire g1_b1__2_n_0;
  wire g1_b1_n_0;
  wire g1_b2__0_n_0;
  wire g1_b2__1_n_0;
  wire g1_b2__2_n_0;
  wire g1_b2_n_0;
  wire g1_b3__0_n_0;
  wire g1_b3__1_n_0;
  wire g1_b3__2_n_0;
  wire g1_b3_n_0;
  wire g1_b4__0_n_0;
  wire g1_b4__1_n_0;
  wire g1_b4__2_n_0;
  wire g1_b4_n_0;
  wire g1_b5__0_n_0;
  wire g1_b5__1_n_0;
  wire g1_b5__2_n_0;
  wire g1_b5_n_0;
  wire g1_b6__0_n_0;
  wire g1_b6__1_n_0;
  wire g1_b6__2_n_0;
  wire g1_b6_n_0;
  wire g1_b7__0_n_0;
  wire g1_b7__1_n_0;
  wire g1_b7__2_n_0;
  wire g1_b7_n_0;
  wire g2_b0__0_n_0;
  wire g2_b0__1_n_0;
  wire g2_b0__2_n_0;
  wire g2_b0_n_0;
  wire g2_b1__0_n_0;
  wire g2_b1__1_n_0;
  wire g2_b1__2_n_0;
  wire g2_b1_n_0;
  wire g2_b2__0_n_0;
  wire g2_b2__1_n_0;
  wire g2_b2__2_n_0;
  wire g2_b2_n_0;
  wire g2_b3__0_n_0;
  wire g2_b3__1_n_0;
  wire g2_b3__2_n_0;
  wire g2_b3_n_0;
  wire g2_b4__0_n_0;
  wire g2_b4__1_n_0;
  wire g2_b4__2_n_0;
  wire g2_b4_n_0;
  wire g2_b5__0_n_0;
  wire g2_b5__1_n_0;
  wire g2_b5__2_n_0;
  wire g2_b5_n_0;
  wire g2_b6__0_n_0;
  wire g2_b6__1_n_0;
  wire g2_b6__2_n_0;
  wire g2_b6_n_0;
  wire g2_b7__0_n_0;
  wire g2_b7__1_n_0;
  wire g2_b7__2_n_0;
  wire g2_b7_n_0;
  wire g3_b0__0_n_0;
  wire g3_b0__1_n_0;
  wire g3_b0__2_n_0;
  wire g3_b0_n_0;
  wire g3_b1__0_n_0;
  wire g3_b1__1_n_0;
  wire g3_b1__2_n_0;
  wire g3_b1_n_0;
  wire g3_b2__0_n_0;
  wire g3_b2__1_n_0;
  wire g3_b2__2_n_0;
  wire g3_b2_n_0;
  wire g3_b3__0_n_0;
  wire g3_b3__1_n_0;
  wire g3_b3__2_n_0;
  wire g3_b3_n_0;
  wire g3_b4__0_n_0;
  wire g3_b4__1_n_0;
  wire g3_b4__2_n_0;
  wire g3_b4_n_0;
  wire g3_b5__0_n_0;
  wire g3_b5__1_n_0;
  wire g3_b5__2_n_0;
  wire g3_b5_n_0;
  wire g3_b6__0_n_0;
  wire g3_b6__1_n_0;
  wire g3_b6__2_n_0;
  wire g3_b6_n_0;
  wire g3_b7__0_n_0;
  wire g3_b7__1_n_0;
  wire g3_b7__2_n_0;
  wire g3_b7_n_0;
  wire g4_b0__0_n_0;
  wire g4_b0__1_n_0;
  wire g4_b0__2_n_0;
  wire g4_b0_n_0;
  wire g4_b1__0_n_0;
  wire g4_b1__1_n_0;
  wire g4_b1__2_n_0;
  wire g4_b1_n_0;
  wire g4_b2__0_n_0;
  wire g4_b2__1_n_0;
  wire g4_b2__2_n_0;
  wire g4_b2_n_0;
  wire g4_b3__0_n_0;
  wire g4_b3__1_n_0;
  wire g4_b3__2_n_0;
  wire g4_b3_n_0;
  wire g4_b4__0_n_0;
  wire g4_b4__1_n_0;
  wire g4_b4__2_n_0;
  wire g4_b4_n_0;
  wire g4_b5__0_n_0;
  wire g4_b5__1_n_0;
  wire g4_b5__2_n_0;
  wire g4_b5_n_0;
  wire g4_b6__0_n_0;
  wire g4_b6__1_n_0;
  wire g4_b6__2_n_0;
  wire g4_b6_n_0;
  wire g4_b7__0_n_0;
  wire g4_b7__1_n_0;
  wire g4_b7__2_n_0;
  wire g4_b7_n_0;
  wire g5_b0__0_n_0;
  wire g5_b0__1_n_0;
  wire g5_b0__2_n_0;
  wire g5_b0_n_0;
  wire g5_b1__0_n_0;
  wire g5_b1__1_n_0;
  wire g5_b1__2_n_0;
  wire g5_b1_n_0;
  wire g5_b2__0_n_0;
  wire g5_b2__1_n_0;
  wire g5_b2__2_n_0;
  wire g5_b2_n_0;
  wire g5_b3__0_n_0;
  wire g5_b3__1_n_0;
  wire g5_b3__2_n_0;
  wire g5_b3_n_0;
  wire g5_b4__0_n_0;
  wire g5_b4__1_n_0;
  wire g5_b4__2_n_0;
  wire g5_b4_n_0;
  wire g5_b5__0_n_0;
  wire g5_b5__1_n_0;
  wire g5_b5__2_n_0;
  wire g5_b5_n_0;
  wire g5_b6__0_n_0;
  wire g5_b6__1_n_0;
  wire g5_b6__2_n_0;
  wire g5_b6_n_0;
  wire g5_b7__0_n_0;
  wire g5_b7__1_n_0;
  wire g5_b7__2_n_0;
  wire g5_b7_n_0;
  wire g6_b0__0_n_0;
  wire g6_b0__1_n_0;
  wire g6_b0__2_n_0;
  wire g6_b0_n_0;
  wire g6_b1__0_n_0;
  wire g6_b1__1_n_0;
  wire g6_b1__2_n_0;
  wire g6_b1_n_0;
  wire g6_b2__0_n_0;
  wire g6_b2__1_n_0;
  wire g6_b2__2_n_0;
  wire g6_b2_n_0;
  wire g6_b3__0_n_0;
  wire g6_b3__1_n_0;
  wire g6_b3__2_n_0;
  wire g6_b3_n_0;
  wire g6_b4__0_n_0;
  wire g6_b4__1_n_0;
  wire g6_b4__2_n_0;
  wire g6_b4_n_0;
  wire g6_b5__0_n_0;
  wire g6_b5__1_n_0;
  wire g6_b5__2_n_0;
  wire g6_b5_n_0;
  wire g6_b6__0_n_0;
  wire g6_b6__1_n_0;
  wire g6_b6__2_n_0;
  wire g6_b6_n_0;
  wire g6_b7__0_n_0;
  wire g6_b7__1_n_0;
  wire g6_b7__2_n_0;
  wire g6_b7_n_0;
  wire g7_b0__0_n_0;
  wire g7_b0__1_n_0;
  wire g7_b0__2_n_0;
  wire g7_b0_n_0;
  wire g7_b1__0_n_0;
  wire g7_b1__1_n_0;
  wire g7_b1__2_n_0;
  wire g7_b1_n_0;
  wire g7_b2__0_n_0;
  wire g7_b2__1_n_0;
  wire g7_b2__2_n_0;
  wire g7_b2_n_0;
  wire g7_b3__0_n_0;
  wire g7_b3__1_n_0;
  wire g7_b3__2_n_0;
  wire g7_b3_n_0;
  wire g7_b4__0_n_0;
  wire g7_b4__1_n_0;
  wire g7_b4__2_n_0;
  wire g7_b4_n_0;
  wire g7_b5__0_n_0;
  wire g7_b5__1_n_0;
  wire g7_b5__2_n_0;
  wire g7_b5_n_0;
  wire g7_b6__0_n_0;
  wire g7_b6__1_n_0;
  wire g7_b6__2_n_0;
  wire g7_b6_n_0;
  wire g7_b7__0_n_0;
  wire g7_b7__1_n_0;
  wire g7_b7__2_n_0;
  wire g7_b7_n_0;
  wire g8_b0__0_n_0;
  wire g8_b0__1_n_0;
  wire g8_b0__2_n_0;
  wire g8_b0_n_0;
  wire g8_b1__0_n_0;
  wire g8_b1__1_n_0;
  wire g8_b1__2_n_0;
  wire g8_b1_n_0;
  wire g8_b2__0_n_0;
  wire g8_b2__1_n_0;
  wire g8_b2__2_n_0;
  wire g8_b2_n_0;
  wire g8_b3__0_n_0;
  wire g8_b3__1_n_0;
  wire g8_b3__2_n_0;
  wire g8_b3_n_0;
  wire g8_b4__0_n_0;
  wire g8_b4__1_n_0;
  wire g8_b4__2_n_0;
  wire g8_b4_n_0;
  wire g8_b6__0_n_0;
  wire g8_b6__1_n_0;
  wire g8_b6__2_n_0;
  wire g8_b6_n_0;
  wire g8_b7__0_n_0;
  wire g8_b7__1_n_0;
  wire g8_b7__2_n_0;
  wire g8_b7_n_0;
  wire g9_b0__0_n_0;
  wire g9_b0__1_n_0;
  wire g9_b0__2_n_0;
  wire g9_b0_n_0;
  wire g9_b1__0_n_0;
  wire g9_b1__1_n_0;
  wire g9_b1__2_n_0;
  wire g9_b1_n_0;
  wire g9_b2__0_n_0;
  wire g9_b2__1_n_0;
  wire g9_b2__2_n_0;
  wire g9_b2_n_0;
  wire g9_b3__0_n_0;
  wire g9_b3__1_n_0;
  wire g9_b3__2_n_0;
  wire g9_b3_n_0;
  wire g9_b4__0_n_0;
  wire g9_b4__1_n_0;
  wire g9_b4__2_n_0;
  wire g9_b4_n_0;
  wire g9_b6__0_n_0;
  wire g9_b6__1_n_0;
  wire g9_b6__2_n_0;
  wire g9_b6_n_0;
  wire g9_b7__0_n_0;
  wire g9_b7__1_n_0;
  wire g9_b7__2_n_0;
  wire g9_b7_n_0;
  wire [9:1]sel;

  IBUF \A_IBUF[0]_inst 
       (.I(A[0]),
        .O(A_IBUF[0]));
  IBUF \A_IBUF[1]_inst 
       (.I(A[1]),
        .O(A_IBUF[1]));
  IBUF \A_IBUF[2]_inst 
       (.I(A[2]),
        .O(A_IBUF[2]));
  IBUF \A_IBUF[3]_inst 
       (.I(A[3]),
        .O(A_IBUF[3]));
  IBUF \A_IBUF[4]_inst 
       (.I(A[4]),
        .O(A_IBUF[4]));
  IBUF \A_IBUF[5]_inst 
       (.I(A[5]),
        .O(A_IBUF[5]));
  IBUF \A_IBUF[6]_inst 
       (.I(A[6]),
        .O(A_IBUF[6]));
  IBUF \A_IBUF[7]_inst 
       (.I(A[7]),
        .O(A_IBUF[7]));
  IBUF \A_IBUF[8]_inst 
       (.I(A[8]),
        .O(A_IBUF[8]));
  IBUF \A_IBUF[9]_inst 
       (.I(A[9]),
        .O(A_IBUF[9]));
  OBUF \RD_OBUF[0]_inst 
       (.I(RD_OBUF[0]),
        .O(RD[0]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[0]_inst_i_1 
       (.I0(\RD_OBUF[0]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[0]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[0]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[0]_inst_i_5_n_0 ),
        .O(RD_OBUF[0]));
  MUXF7 \RD_OBUF[0]_inst_i_10 
       (.I0(g4_b0_n_0),
        .I1(g5_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[0]_inst_i_11 
       (.I0(g6_b0_n_0),
        .I1(g7_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[0]_inst_i_12 
       (.I0(g0_b0_n_0),
        .I1(g1_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[0]_inst_i_13 
       (.I0(g2_b0_n_0),
        .I1(g3_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[0]_inst_i_2 
       (.I0(\RD_OBUF[0]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[0]_inst_i_7_n_0 ),
        .O(\RD_OBUF[0]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[0]_inst_i_3 
       (.I0(\RD_OBUF[0]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[0]_inst_i_9_n_0 ),
        .O(\RD_OBUF[0]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[0]_inst_i_4 
       (.I0(\RD_OBUF[0]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[0]_inst_i_11_n_0 ),
        .O(\RD_OBUF[0]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[0]_inst_i_5 
       (.I0(\RD_OBUF[0]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[0]_inst_i_13_n_0 ),
        .O(\RD_OBUF[0]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[0]_inst_i_6 
       (.I0(g12_b0_n_0),
        .I1(g13_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[0]_inst_i_7 
       (.I0(g14_b0_n_0),
        .I1(g15_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[0]_inst_i_8 
       (.I0(g8_b0_n_0),
        .I1(g9_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[0]_inst_i_9 
       (.I0(g10_b0_n_0),
        .I1(g11_b0_n_0),
        .O(\RD_OBUF[0]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[10]_inst 
       (.I(RD_OBUF[10]),
        .O(RD[10]));
  MUXF7 \RD_OBUF[10]_inst_i_1 
       (.I0(\RD_OBUF[10]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[10]_inst_i_3_n_0 ),
        .O(RD_OBUF[10]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_10 
       (.I0(g11_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_11 
       (.I0(g9_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[10]_inst_i_2 
       (.I0(\RD_OBUF[10]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[10]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[10]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[10]_inst_i_7_n_0 ),
        .O(\RD_OBUF[10]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[10]_inst_i_3 
       (.I0(\RD_OBUF[10]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[10]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[10]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[10]_inst_i_11_n_0 ),
        .O(\RD_OBUF[10]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_4 
       (.I0(g7_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_5 
       (.I0(g5_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_6 
       (.I0(g3_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_7 
       (.I0(g1_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_8 
       (.I0(g15_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[10]_inst_i_9 
       (.I0(g13_b2__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b2__2_n_0),
        .O(\RD_OBUF[10]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[11]_inst 
       (.I(RD_OBUF[11]),
        .O(RD[11]));
  MUXF7 \RD_OBUF[11]_inst_i_1 
       (.I0(\RD_OBUF[11]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[11]_inst_i_3_n_0 ),
        .O(RD_OBUF[11]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_10 
       (.I0(g11_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_11 
       (.I0(g9_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[11]_inst_i_2 
       (.I0(\RD_OBUF[11]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[11]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[11]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[11]_inst_i_7_n_0 ),
        .O(\RD_OBUF[11]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[11]_inst_i_3 
       (.I0(\RD_OBUF[11]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[11]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[11]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[11]_inst_i_11_n_0 ),
        .O(\RD_OBUF[11]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_4 
       (.I0(g7_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_5 
       (.I0(g5_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_6 
       (.I0(g3_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_7 
       (.I0(g1_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_8 
       (.I0(g15_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[11]_inst_i_9 
       (.I0(g13_b3__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b3__2_n_0),
        .O(\RD_OBUF[11]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[12]_inst 
       (.I(RD_OBUF[12]),
        .O(RD[12]));
  MUXF7 \RD_OBUF[12]_inst_i_1 
       (.I0(\RD_OBUF[12]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[12]_inst_i_3_n_0 ),
        .O(RD_OBUF[12]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_10 
       (.I0(g11_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_11 
       (.I0(g9_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[12]_inst_i_2 
       (.I0(\RD_OBUF[12]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[12]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[12]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[12]_inst_i_7_n_0 ),
        .O(\RD_OBUF[12]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[12]_inst_i_3 
       (.I0(\RD_OBUF[12]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[12]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[12]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[12]_inst_i_11_n_0 ),
        .O(\RD_OBUF[12]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_4 
       (.I0(g7_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_5 
       (.I0(g5_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_6 
       (.I0(g3_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_7 
       (.I0(g1_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_8 
       (.I0(g15_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[12]_inst_i_9 
       (.I0(g13_b4__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b4__2_n_0),
        .O(\RD_OBUF[12]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[13]_inst 
       (.I(RD_OBUF[13]),
        .O(RD[13]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[13]_inst_i_1 
       (.I0(\RD_OBUF[13]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[13]_inst_i_3_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[13]_inst_i_5_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[13]_inst_i_7_n_0 ),
        .O(RD_OBUF[13]));
  MUXF7 \RD_OBUF[13]_inst_i_2 
       (.I0(g6_b5__2_n_0),
        .I1(g7_b5__2_n_0),
        .O(\RD_OBUF[13]_inst_i_2_n_0 ),
        .S(\RD_OBUF[13]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[13]_inst_i_3 
       (.I0(g4_b5__2_n_0),
        .I1(g5_b5__2_n_0),
        .O(\RD_OBUF[13]_inst_i_3_n_0 ),
        .S(\RD_OBUF[13]_inst_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \RD_OBUF[13]_inst_i_4 
       (.I0(A_IBUF[6]),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[7]),
        .I3(A_IBUF[8]),
        .O(\RD_OBUF[13]_inst_i_4_n_0 ));
  MUXF7 \RD_OBUF[13]_inst_i_5 
       (.I0(g2_b5__2_n_0),
        .I1(g3_b5__2_n_0),
        .O(\RD_OBUF[13]_inst_i_5_n_0 ),
        .S(\RD_OBUF[13]_inst_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \RD_OBUF[13]_inst_i_6 
       (.I0(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I1(A_IBUF[6]),
        .I2(A_IBUF[7]),
        .O(\RD_OBUF[13]_inst_i_6_n_0 ));
  MUXF7 \RD_OBUF[13]_inst_i_7 
       (.I0(g0_b5__2_n_0),
        .I1(g1_b5__2_n_0),
        .O(\RD_OBUF[13]_inst_i_7_n_0 ),
        .S(\RD_OBUF[13]_inst_i_8_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \RD_OBUF[13]_inst_i_8 
       (.I0(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I1(A_IBUF[6]),
        .O(\RD_OBUF[13]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[14]_inst 
       (.I(RD_OBUF[14]),
        .O(RD[14]));
  MUXF7 \RD_OBUF[14]_inst_i_1 
       (.I0(\RD_OBUF[14]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[14]_inst_i_3_n_0 ),
        .O(RD_OBUF[14]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_10 
       (.I0(g11_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_11 
       (.I0(g9_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[14]_inst_i_2 
       (.I0(\RD_OBUF[14]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[14]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[14]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[14]_inst_i_7_n_0 ),
        .O(\RD_OBUF[14]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[14]_inst_i_3 
       (.I0(\RD_OBUF[14]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[14]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[14]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[14]_inst_i_11_n_0 ),
        .O(\RD_OBUF[14]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_4 
       (.I0(g7_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_5 
       (.I0(g5_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_6 
       (.I0(g3_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_7 
       (.I0(g1_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_8 
       (.I0(g15_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[14]_inst_i_9 
       (.I0(g13_b6__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b6__2_n_0),
        .O(\RD_OBUF[14]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[15]_inst 
       (.I(RD_OBUF[15]),
        .O(RD[15]));
  MUXF7 \RD_OBUF[15]_inst_i_1 
       (.I0(\RD_OBUF[15]_inst_i_3_n_0 ),
        .I1(\RD_OBUF[15]_inst_i_4_n_0 ),
        .O(RD_OBUF[15]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_10 
       (.I0(g15_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_11 
       (.I0(g13_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_11_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_12 
       (.I0(g11_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_12_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_13 
       (.I0(g9_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_13_n_0 ));
  LUT5 #(
    .INIT(32'h7FFF8000)) 
    \RD_OBUF[15]_inst_i_2 
       (.I0(A_IBUF[7]),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(A_IBUF[8]),
        .I4(A_IBUF[9]),
        .O(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[15]_inst_i_3 
       (.I0(\RD_OBUF[15]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[15]_inst_i_7_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[15]_inst_i_8_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[15]_inst_i_9_n_0 ),
        .O(\RD_OBUF[15]_inst_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[15]_inst_i_4 
       (.I0(\RD_OBUF[15]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[15]_inst_i_11_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[15]_inst_i_12_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[15]_inst_i_13_n_0 ),
        .O(\RD_OBUF[15]_inst_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h8000000000000000)) 
    \RD_OBUF[15]_inst_i_5 
       (.I0(A_IBUF[5]),
        .I1(A_IBUF[3]),
        .I2(A_IBUF[1]),
        .I3(A_IBUF[0]),
        .I4(A_IBUF[2]),
        .I5(A_IBUF[4]),
        .O(\RD_OBUF[15]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_6 
       (.I0(g7_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_7 
       (.I0(g5_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_8 
       (.I0(g3_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[15]_inst_i_9 
       (.I0(g1_b7__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b7__2_n_0),
        .O(\RD_OBUF[15]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[16]_inst 
       (.I(RD_OBUF[16]),
        .O(RD[16]));
  MUXF7 \RD_OBUF[16]_inst_i_1 
       (.I0(\RD_OBUF[16]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[16]_inst_i_3_n_0 ),
        .O(RD_OBUF[16]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_10 
       (.I0(g10_b0__0_n_0),
        .I1(g11_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_11 
       (.I0(g8_b0__0_n_0),
        .I1(g9_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[16]_inst_i_2 
       (.I0(\RD_OBUF[16]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[16]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[16]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[16]_inst_i_7_n_0 ),
        .O(\RD_OBUF[16]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[16]_inst_i_3 
       (.I0(\RD_OBUF[16]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[16]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[16]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[16]_inst_i_11_n_0 ),
        .O(\RD_OBUF[16]_inst_i_3_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_4 
       (.I0(g6_b0__0_n_0),
        .I1(g7_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_4_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_5 
       (.I0(g4_b0__0_n_0),
        .I1(g5_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_6 
       (.I0(g2_b0__0_n_0),
        .I1(g3_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_7 
       (.I0(g0_b0__0_n_0),
        .I1(g1_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_8 
       (.I0(g14_b0__0_n_0),
        .I1(g15_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[16]_inst_i_9 
       (.I0(g12_b0__0_n_0),
        .I1(g13_b0__0_n_0),
        .O(\RD_OBUF[16]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[17]_inst 
       (.I(RD_OBUF[17]),
        .O(RD[17]));
  MUXF7 \RD_OBUF[17]_inst_i_1 
       (.I0(\RD_OBUF[17]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[17]_inst_i_3_n_0 ),
        .O(RD_OBUF[17]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_10 
       (.I0(g10_b1__0_n_0),
        .I1(g11_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_11 
       (.I0(g8_b1__0_n_0),
        .I1(g9_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[17]_inst_i_2 
       (.I0(\RD_OBUF[17]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[17]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[17]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[17]_inst_i_7_n_0 ),
        .O(\RD_OBUF[17]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[17]_inst_i_3 
       (.I0(\RD_OBUF[17]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[17]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[17]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[17]_inst_i_11_n_0 ),
        .O(\RD_OBUF[17]_inst_i_3_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_4 
       (.I0(g6_b1__0_n_0),
        .I1(g7_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_4_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_5 
       (.I0(g4_b1__0_n_0),
        .I1(g5_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_6 
       (.I0(g2_b1__0_n_0),
        .I1(g3_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_7 
       (.I0(g0_b1__0_n_0),
        .I1(g1_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_8 
       (.I0(g14_b1__0_n_0),
        .I1(g15_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[17]_inst_i_9 
       (.I0(g12_b1__0_n_0),
        .I1(g13_b1__0_n_0),
        .O(\RD_OBUF[17]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[18]_inst 
       (.I(RD_OBUF[18]),
        .O(RD[18]));
  MUXF7 \RD_OBUF[18]_inst_i_1 
       (.I0(\RD_OBUF[18]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[18]_inst_i_3_n_0 ),
        .O(RD_OBUF[18]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_10 
       (.I0(g10_b2__0_n_0),
        .I1(g11_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_11 
       (.I0(g8_b2__0_n_0),
        .I1(g9_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[18]_inst_i_2 
       (.I0(\RD_OBUF[18]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[18]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[18]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[18]_inst_i_7_n_0 ),
        .O(\RD_OBUF[18]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[18]_inst_i_3 
       (.I0(\RD_OBUF[18]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[18]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[18]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[18]_inst_i_11_n_0 ),
        .O(\RD_OBUF[18]_inst_i_3_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_4 
       (.I0(g6_b2__0_n_0),
        .I1(g7_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_4_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_5 
       (.I0(g4_b2__0_n_0),
        .I1(g5_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_6 
       (.I0(g2_b2__0_n_0),
        .I1(g3_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_7 
       (.I0(g0_b2__0_n_0),
        .I1(g1_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_8 
       (.I0(g14_b2__0_n_0),
        .I1(g15_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[18]_inst_i_9 
       (.I0(g12_b2__0_n_0),
        .I1(g13_b2__0_n_0),
        .O(\RD_OBUF[18]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[19]_inst 
       (.I(RD_OBUF[19]),
        .O(RD[19]));
  MUXF7 \RD_OBUF[19]_inst_i_1 
       (.I0(\RD_OBUF[19]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[19]_inst_i_3_n_0 ),
        .O(RD_OBUF[19]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_10 
       (.I0(g10_b3__0_n_0),
        .I1(g11_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_11 
       (.I0(g8_b3__0_n_0),
        .I1(g9_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[19]_inst_i_2 
       (.I0(\RD_OBUF[19]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[19]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[19]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[19]_inst_i_7_n_0 ),
        .O(\RD_OBUF[19]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[19]_inst_i_3 
       (.I0(\RD_OBUF[19]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[19]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[19]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[19]_inst_i_11_n_0 ),
        .O(\RD_OBUF[19]_inst_i_3_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_4 
       (.I0(g6_b3__0_n_0),
        .I1(g7_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_4_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_5 
       (.I0(g4_b3__0_n_0),
        .I1(g5_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_6 
       (.I0(g2_b3__0_n_0),
        .I1(g3_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_7 
       (.I0(g0_b3__0_n_0),
        .I1(g1_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_8 
       (.I0(g14_b3__0_n_0),
        .I1(g15_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[19]_inst_i_9 
       (.I0(g12_b3__0_n_0),
        .I1(g13_b3__0_n_0),
        .O(\RD_OBUF[19]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[1]_inst 
       (.I(RD_OBUF[1]),
        .O(RD[1]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[1]_inst_i_1 
       (.I0(\RD_OBUF[1]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[1]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[1]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[1]_inst_i_5_n_0 ),
        .O(RD_OBUF[1]));
  MUXF7 \RD_OBUF[1]_inst_i_10 
       (.I0(g4_b1_n_0),
        .I1(g5_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[1]_inst_i_11 
       (.I0(g6_b1_n_0),
        .I1(g7_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[1]_inst_i_12 
       (.I0(g0_b1_n_0),
        .I1(g1_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[1]_inst_i_13 
       (.I0(g2_b1_n_0),
        .I1(g3_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[1]_inst_i_2 
       (.I0(\RD_OBUF[1]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[1]_inst_i_7_n_0 ),
        .O(\RD_OBUF[1]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[1]_inst_i_3 
       (.I0(\RD_OBUF[1]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[1]_inst_i_9_n_0 ),
        .O(\RD_OBUF[1]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[1]_inst_i_4 
       (.I0(\RD_OBUF[1]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[1]_inst_i_11_n_0 ),
        .O(\RD_OBUF[1]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[1]_inst_i_5 
       (.I0(\RD_OBUF[1]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[1]_inst_i_13_n_0 ),
        .O(\RD_OBUF[1]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[1]_inst_i_6 
       (.I0(g12_b1_n_0),
        .I1(g13_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[1]_inst_i_7 
       (.I0(g14_b1_n_0),
        .I1(g15_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[1]_inst_i_8 
       (.I0(g8_b1_n_0),
        .I1(g9_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[1]_inst_i_9 
       (.I0(g10_b1_n_0),
        .I1(g11_b1_n_0),
        .O(\RD_OBUF[1]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[20]_inst 
       (.I(RD_OBUF[20]),
        .O(RD[20]));
  MUXF7 \RD_OBUF[20]_inst_i_1 
       (.I0(\RD_OBUF[20]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[20]_inst_i_3_n_0 ),
        .O(RD_OBUF[20]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_10 
       (.I0(g10_b4__0_n_0),
        .I1(g11_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_11 
       (.I0(g8_b4__0_n_0),
        .I1(g9_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[20]_inst_i_2 
       (.I0(\RD_OBUF[20]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[20]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[20]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[20]_inst_i_7_n_0 ),
        .O(\RD_OBUF[20]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[20]_inst_i_3 
       (.I0(\RD_OBUF[20]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[20]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[20]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[20]_inst_i_11_n_0 ),
        .O(\RD_OBUF[20]_inst_i_3_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_4 
       (.I0(g6_b4__0_n_0),
        .I1(g7_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_4_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_5 
       (.I0(g4_b4__0_n_0),
        .I1(g5_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_6 
       (.I0(g2_b4__0_n_0),
        .I1(g3_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_7 
       (.I0(g0_b4__0_n_0),
        .I1(g1_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_8 
       (.I0(g14_b4__0_n_0),
        .I1(g15_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[20]_inst_i_9 
       (.I0(g12_b4__0_n_0),
        .I1(g13_b4__0_n_0),
        .O(\RD_OBUF[20]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[21]_inst 
       (.I(RD_OBUF[21]),
        .O(RD[21]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[21]_inst_i_1 
       (.I0(\RD_OBUF[21]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[21]_inst_i_3_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[21]_inst_i_5_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[21]_inst_i_7_n_0 ),
        .O(RD_OBUF[21]));
  MUXF7 \RD_OBUF[21]_inst_i_2 
       (.I0(g6_b5__0_n_0),
        .I1(g7_b5__0_n_0),
        .O(\RD_OBUF[21]_inst_i_2_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[21]_inst_i_3 
       (.I0(g4_b5__0_n_0),
        .I1(g5_b5__0_n_0),
        .O(\RD_OBUF[21]_inst_i_3_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \RD_OBUF[21]_inst_i_4 
       (.I0(\RD_OBUF[23]_inst_i_5_n_0 ),
        .I1(A_IBUF[7]),
        .I2(A_IBUF[8]),
        .O(\RD_OBUF[21]_inst_i_4_n_0 ));
  MUXF7 \RD_OBUF[21]_inst_i_5 
       (.I0(g2_b5__0_n_0),
        .I1(g3_b5__0_n_0),
        .O(\RD_OBUF[21]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \RD_OBUF[21]_inst_i_6 
       (.I0(\RD_OBUF[23]_inst_i_5_n_0 ),
        .I1(A_IBUF[7]),
        .O(\RD_OBUF[21]_inst_i_6_n_0 ));
  MUXF7 \RD_OBUF[21]_inst_i_7 
       (.I0(g0_b5__0_n_0),
        .I1(g1_b5__0_n_0),
        .O(\RD_OBUF[21]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'h7FFFFFFF80000000)) 
    \RD_OBUF[21]_inst_i_8 
       (.I0(A_IBUF[4]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[1]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[5]),
        .I5(A_IBUF[6]),
        .O(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[22]_inst 
       (.I(RD_OBUF[22]),
        .O(RD[22]));
  MUXF7 \RD_OBUF[22]_inst_i_1 
       (.I0(\RD_OBUF[22]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[22]_inst_i_3_n_0 ),
        .O(RD_OBUF[22]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_10 
       (.I0(g10_b6__0_n_0),
        .I1(g11_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_11 
       (.I0(g8_b6__0_n_0),
        .I1(g9_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[22]_inst_i_2 
       (.I0(\RD_OBUF[22]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[22]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[22]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[22]_inst_i_7_n_0 ),
        .O(\RD_OBUF[22]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[22]_inst_i_3 
       (.I0(\RD_OBUF[22]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[22]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[22]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[22]_inst_i_11_n_0 ),
        .O(\RD_OBUF[22]_inst_i_3_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_4 
       (.I0(g6_b6__0_n_0),
        .I1(g7_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_4_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_5 
       (.I0(g4_b6__0_n_0),
        .I1(g5_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_5_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_6 
       (.I0(g2_b6__0_n_0),
        .I1(g3_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_7 
       (.I0(g0_b6__0_n_0),
        .I1(g1_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_8 
       (.I0(g14_b6__0_n_0),
        .I1(g15_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[22]_inst_i_9 
       (.I0(g12_b6__0_n_0),
        .I1(g13_b6__0_n_0),
        .O(\RD_OBUF[22]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[23]_inst 
       (.I(RD_OBUF[23]),
        .O(RD[23]));
  MUXF7 \RD_OBUF[23]_inst_i_1 
       (.I0(\RD_OBUF[23]_inst_i_3_n_0 ),
        .I1(\RD_OBUF[23]_inst_i_4_n_0 ),
        .O(RD_OBUF[23]),
        .S(\RD_OBUF[23]_inst_i_2_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_10 
       (.I0(g14_b7__0_n_0),
        .I1(g15_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_10_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_11 
       (.I0(g12_b7__0_n_0),
        .I1(g13_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_11_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_12 
       (.I0(g10_b7__0_n_0),
        .I1(g11_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_12_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_13 
       (.I0(g8_b7__0_n_0),
        .I1(g9_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_13_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'h7F80)) 
    \RD_OBUF[23]_inst_i_2 
       (.I0(A_IBUF[7]),
        .I1(\RD_OBUF[23]_inst_i_5_n_0 ),
        .I2(A_IBUF[8]),
        .I3(A_IBUF[9]),
        .O(\RD_OBUF[23]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[23]_inst_i_3 
       (.I0(\RD_OBUF[23]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[23]_inst_i_7_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[23]_inst_i_8_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[23]_inst_i_9_n_0 ),
        .O(\RD_OBUF[23]_inst_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[23]_inst_i_4 
       (.I0(\RD_OBUF[23]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[23]_inst_i_11_n_0 ),
        .I2(\RD_OBUF[21]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[23]_inst_i_12_n_0 ),
        .I4(\RD_OBUF[21]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[23]_inst_i_13_n_0 ),
        .O(\RD_OBUF[23]_inst_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h8000000000000000)) 
    \RD_OBUF[23]_inst_i_5 
       (.I0(A_IBUF[6]),
        .I1(A_IBUF[4]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[1]),
        .I4(A_IBUF[3]),
        .I5(A_IBUF[5]),
        .O(\RD_OBUF[23]_inst_i_5_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_6 
       (.I0(g6_b7__0_n_0),
        .I1(g7_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_6_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_7 
       (.I0(g4_b7__0_n_0),
        .I1(g5_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_7_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_8 
       (.I0(g2_b7__0_n_0),
        .I1(g3_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_8_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  MUXF7 \RD_OBUF[23]_inst_i_9 
       (.I0(g0_b7__0_n_0),
        .I1(g1_b7__0_n_0),
        .O(\RD_OBUF[23]_inst_i_9_n_0 ),
        .S(\RD_OBUF[21]_inst_i_8_n_0 ));
  OBUF \RD_OBUF[24]_inst 
       (.I(RD_OBUF[24]),
        .O(RD[24]));
  MUXF7 \RD_OBUF[24]_inst_i_1 
       (.I0(\RD_OBUF[24]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[24]_inst_i_3_n_0 ),
        .O(RD_OBUF[24]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_10 
       (.I0(g11_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_11 
       (.I0(g9_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[24]_inst_i_2 
       (.I0(\RD_OBUF[24]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[24]_inst_i_5_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[24]_inst_i_6_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[24]_inst_i_7_n_0 ),
        .O(\RD_OBUF[24]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[24]_inst_i_3 
       (.I0(\RD_OBUF[24]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[24]_inst_i_9_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[24]_inst_i_10_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[24]_inst_i_11_n_0 ),
        .O(\RD_OBUF[24]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_4 
       (.I0(g7_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_5 
       (.I0(g5_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_6 
       (.I0(g3_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_7 
       (.I0(g1_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_8 
       (.I0(g15_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[24]_inst_i_9 
       (.I0(g13_b0__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b0__1_n_0),
        .O(\RD_OBUF[24]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[25]_inst 
       (.I(RD_OBUF[25]),
        .O(RD[25]));
  MUXF7 \RD_OBUF[25]_inst_i_1 
       (.I0(\RD_OBUF[25]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[25]_inst_i_3_n_0 ),
        .O(RD_OBUF[25]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_10 
       (.I0(g11_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_11 
       (.I0(g9_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[25]_inst_i_2 
       (.I0(\RD_OBUF[25]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[25]_inst_i_5_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[25]_inst_i_6_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[25]_inst_i_7_n_0 ),
        .O(\RD_OBUF[25]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[25]_inst_i_3 
       (.I0(\RD_OBUF[25]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[25]_inst_i_9_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[25]_inst_i_10_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[25]_inst_i_11_n_0 ),
        .O(\RD_OBUF[25]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_4 
       (.I0(g7_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_5 
       (.I0(g5_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_6 
       (.I0(g3_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_7 
       (.I0(g1_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_8 
       (.I0(g15_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[25]_inst_i_9 
       (.I0(g13_b1__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b1__1_n_0),
        .O(\RD_OBUF[25]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[26]_inst 
       (.I(RD_OBUF[26]),
        .O(RD[26]));
  MUXF7 \RD_OBUF[26]_inst_i_1 
       (.I0(\RD_OBUF[26]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[26]_inst_i_3_n_0 ),
        .O(RD_OBUF[26]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_10 
       (.I0(g11_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_11 
       (.I0(g9_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[26]_inst_i_2 
       (.I0(\RD_OBUF[26]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[26]_inst_i_5_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[26]_inst_i_6_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[26]_inst_i_7_n_0 ),
        .O(\RD_OBUF[26]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[26]_inst_i_3 
       (.I0(\RD_OBUF[26]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[26]_inst_i_9_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[26]_inst_i_10_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[26]_inst_i_11_n_0 ),
        .O(\RD_OBUF[26]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_4 
       (.I0(g7_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_5 
       (.I0(g5_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_6 
       (.I0(g3_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_7 
       (.I0(g1_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_8 
       (.I0(g15_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[26]_inst_i_9 
       (.I0(g13_b2__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b2__1_n_0),
        .O(\RD_OBUF[26]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[27]_inst 
       (.I(RD_OBUF[27]),
        .O(RD[27]));
  MUXF7 \RD_OBUF[27]_inst_i_1 
       (.I0(\RD_OBUF[27]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[27]_inst_i_3_n_0 ),
        .O(RD_OBUF[27]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_10 
       (.I0(g11_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_11 
       (.I0(g9_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[27]_inst_i_2 
       (.I0(\RD_OBUF[27]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[27]_inst_i_5_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[27]_inst_i_6_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[27]_inst_i_7_n_0 ),
        .O(\RD_OBUF[27]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[27]_inst_i_3 
       (.I0(\RD_OBUF[27]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[27]_inst_i_9_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[27]_inst_i_10_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[27]_inst_i_11_n_0 ),
        .O(\RD_OBUF[27]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_4 
       (.I0(g7_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_5 
       (.I0(g5_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_6 
       (.I0(g3_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_7 
       (.I0(g1_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_8 
       (.I0(g15_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[27]_inst_i_9 
       (.I0(g13_b3__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b3__1_n_0),
        .O(\RD_OBUF[27]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[28]_inst 
       (.I(RD_OBUF[28]),
        .O(RD[28]));
  MUXF7 \RD_OBUF[28]_inst_i_1 
       (.I0(\RD_OBUF[28]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[28]_inst_i_3_n_0 ),
        .O(RD_OBUF[28]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_10 
       (.I0(g11_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_11 
       (.I0(g9_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[28]_inst_i_2 
       (.I0(\RD_OBUF[28]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[28]_inst_i_5_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[28]_inst_i_6_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[28]_inst_i_7_n_0 ),
        .O(\RD_OBUF[28]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[28]_inst_i_3 
       (.I0(\RD_OBUF[28]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[28]_inst_i_9_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[28]_inst_i_10_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[28]_inst_i_11_n_0 ),
        .O(\RD_OBUF[28]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_4 
       (.I0(g7_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_5 
       (.I0(g5_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_6 
       (.I0(g3_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_7 
       (.I0(g1_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_8 
       (.I0(g15_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[28]_inst_i_9 
       (.I0(g13_b4__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b4__1_n_0),
        .O(\RD_OBUF[28]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[29]_inst 
       (.I(RD_OBUF[29]),
        .O(RD[29]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[29]_inst_i_1 
       (.I0(\RD_OBUF[29]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[29]_inst_i_3_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[29]_inst_i_5_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[29]_inst_i_7_n_0 ),
        .O(RD_OBUF[29]));
  MUXF7 \RD_OBUF[29]_inst_i_2 
       (.I0(g6_b5__1_n_0),
        .I1(g7_b5__1_n_0),
        .O(\RD_OBUF[29]_inst_i_2_n_0 ),
        .S(sel[6]));
  MUXF7 \RD_OBUF[29]_inst_i_3 
       (.I0(g4_b5__1_n_0),
        .I1(g5_b5__1_n_0),
        .O(\RD_OBUF[29]_inst_i_3_n_0 ),
        .S(sel[6]));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \RD_OBUF[29]_inst_i_4 
       (.I0(A_IBUF[6]),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[7]),
        .I3(A_IBUF[8]),
        .O(sel[8]));
  MUXF7 \RD_OBUF[29]_inst_i_5 
       (.I0(g2_b5__1_n_0),
        .I1(g3_b5__1_n_0),
        .O(\RD_OBUF[29]_inst_i_5_n_0 ),
        .S(sel[6]));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \RD_OBUF[29]_inst_i_6 
       (.I0(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I1(A_IBUF[6]),
        .I2(A_IBUF[7]),
        .O(sel[7]));
  MUXF7 \RD_OBUF[29]_inst_i_7 
       (.I0(g0_b5__1_n_0),
        .I1(g1_b5__1_n_0),
        .O(\RD_OBUF[29]_inst_i_7_n_0 ),
        .S(sel[6]));
  LUT2 #(
    .INIT(4'h6)) 
    \RD_OBUF[29]_inst_i_8 
       (.I0(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I1(A_IBUF[6]),
        .O(sel[6]));
  OBUF \RD_OBUF[2]_inst 
       (.I(RD_OBUF[2]),
        .O(RD[2]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[2]_inst_i_1 
       (.I0(\RD_OBUF[2]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[2]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[2]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[2]_inst_i_5_n_0 ),
        .O(RD_OBUF[2]));
  MUXF7 \RD_OBUF[2]_inst_i_10 
       (.I0(g4_b2_n_0),
        .I1(g5_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[2]_inst_i_11 
       (.I0(g6_b2_n_0),
        .I1(g7_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[2]_inst_i_12 
       (.I0(g0_b2_n_0),
        .I1(g1_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[2]_inst_i_13 
       (.I0(g2_b2_n_0),
        .I1(g3_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[2]_inst_i_2 
       (.I0(\RD_OBUF[2]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[2]_inst_i_7_n_0 ),
        .O(\RD_OBUF[2]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[2]_inst_i_3 
       (.I0(\RD_OBUF[2]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[2]_inst_i_9_n_0 ),
        .O(\RD_OBUF[2]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[2]_inst_i_4 
       (.I0(\RD_OBUF[2]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[2]_inst_i_11_n_0 ),
        .O(\RD_OBUF[2]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[2]_inst_i_5 
       (.I0(\RD_OBUF[2]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[2]_inst_i_13_n_0 ),
        .O(\RD_OBUF[2]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[2]_inst_i_6 
       (.I0(g12_b2_n_0),
        .I1(g13_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[2]_inst_i_7 
       (.I0(g14_b2_n_0),
        .I1(g15_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[2]_inst_i_8 
       (.I0(g8_b2_n_0),
        .I1(g9_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[2]_inst_i_9 
       (.I0(g10_b2_n_0),
        .I1(g11_b2_n_0),
        .O(\RD_OBUF[2]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[30]_inst 
       (.I(RD_OBUF[30]),
        .O(RD[30]));
  MUXF7 \RD_OBUF[30]_inst_i_1 
       (.I0(\RD_OBUF[30]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[30]_inst_i_3_n_0 ),
        .O(RD_OBUF[30]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_10 
       (.I0(g11_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_11 
       (.I0(g9_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[30]_inst_i_2 
       (.I0(\RD_OBUF[30]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[30]_inst_i_5_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[30]_inst_i_6_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[30]_inst_i_7_n_0 ),
        .O(\RD_OBUF[30]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[30]_inst_i_3 
       (.I0(\RD_OBUF[30]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[30]_inst_i_9_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[30]_inst_i_10_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[30]_inst_i_11_n_0 ),
        .O(\RD_OBUF[30]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_4 
       (.I0(g7_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_5 
       (.I0(g5_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_6 
       (.I0(g3_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_7 
       (.I0(g1_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_8 
       (.I0(g15_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[30]_inst_i_9 
       (.I0(g13_b6__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b6__1_n_0),
        .O(\RD_OBUF[30]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[31]_inst 
       (.I(RD_OBUF[31]),
        .O(RD[31]));
  MUXF7 \RD_OBUF[31]_inst_i_1 
       (.I0(\RD_OBUF[31]_inst_i_3_n_0 ),
        .I1(\RD_OBUF[31]_inst_i_4_n_0 ),
        .O(RD_OBUF[31]),
        .S(sel[9]));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_10 
       (.I0(g15_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_11 
       (.I0(g13_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_11_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_12 
       (.I0(g11_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_12_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_13 
       (.I0(g9_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_13_n_0 ));
  LUT5 #(
    .INIT(32'h7FFF8000)) 
    \RD_OBUF[31]_inst_i_2 
       (.I0(A_IBUF[7]),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(A_IBUF[8]),
        .I4(A_IBUF[9]),
        .O(sel[9]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[31]_inst_i_3 
       (.I0(\RD_OBUF[31]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[31]_inst_i_7_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[31]_inst_i_8_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[31]_inst_i_9_n_0 ),
        .O(\RD_OBUF[31]_inst_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[31]_inst_i_4 
       (.I0(\RD_OBUF[31]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[31]_inst_i_11_n_0 ),
        .I2(sel[8]),
        .I3(\RD_OBUF[31]_inst_i_12_n_0 ),
        .I4(sel[7]),
        .I5(\RD_OBUF[31]_inst_i_13_n_0 ),
        .O(\RD_OBUF[31]_inst_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h8880000000000000)) 
    \RD_OBUF[31]_inst_i_5 
       (.I0(A_IBUF[5]),
        .I1(A_IBUF[3]),
        .I2(A_IBUF[0]),
        .I3(A_IBUF[1]),
        .I4(A_IBUF[2]),
        .I5(A_IBUF[4]),
        .O(\RD_OBUF[31]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_6 
       (.I0(g7_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_7 
       (.I0(g5_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_8 
       (.I0(g3_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[31]_inst_i_9 
       (.I0(g1_b7__1_n_0),
        .I1(\RD_OBUF[31]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b7__1_n_0),
        .O(\RD_OBUF[31]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[3]_inst 
       (.I(RD_OBUF[3]),
        .O(RD[3]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[3]_inst_i_1 
       (.I0(\RD_OBUF[3]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[3]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[3]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[3]_inst_i_5_n_0 ),
        .O(RD_OBUF[3]));
  MUXF7 \RD_OBUF[3]_inst_i_10 
       (.I0(g4_b3_n_0),
        .I1(g5_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[3]_inst_i_11 
       (.I0(g6_b3_n_0),
        .I1(g7_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[3]_inst_i_12 
       (.I0(g0_b3_n_0),
        .I1(g1_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[3]_inst_i_13 
       (.I0(g2_b3_n_0),
        .I1(g3_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[3]_inst_i_2 
       (.I0(\RD_OBUF[3]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[3]_inst_i_7_n_0 ),
        .O(\RD_OBUF[3]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[3]_inst_i_3 
       (.I0(\RD_OBUF[3]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[3]_inst_i_9_n_0 ),
        .O(\RD_OBUF[3]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[3]_inst_i_4 
       (.I0(\RD_OBUF[3]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[3]_inst_i_11_n_0 ),
        .O(\RD_OBUF[3]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[3]_inst_i_5 
       (.I0(\RD_OBUF[3]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[3]_inst_i_13_n_0 ),
        .O(\RD_OBUF[3]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[3]_inst_i_6 
       (.I0(g12_b3_n_0),
        .I1(g13_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[3]_inst_i_7 
       (.I0(g14_b3_n_0),
        .I1(g15_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[3]_inst_i_8 
       (.I0(g8_b3_n_0),
        .I1(g9_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[3]_inst_i_9 
       (.I0(g10_b3_n_0),
        .I1(g11_b3_n_0),
        .O(\RD_OBUF[3]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[4]_inst 
       (.I(RD_OBUF[4]),
        .O(RD[4]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[4]_inst_i_1 
       (.I0(\RD_OBUF[4]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[4]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[4]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[4]_inst_i_5_n_0 ),
        .O(RD_OBUF[4]));
  MUXF7 \RD_OBUF[4]_inst_i_10 
       (.I0(g4_b4_n_0),
        .I1(g5_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[4]_inst_i_11 
       (.I0(g6_b4_n_0),
        .I1(g7_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[4]_inst_i_12 
       (.I0(g0_b4_n_0),
        .I1(g1_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[4]_inst_i_13 
       (.I0(g2_b4_n_0),
        .I1(g3_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[4]_inst_i_2 
       (.I0(\RD_OBUF[4]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[4]_inst_i_7_n_0 ),
        .O(\RD_OBUF[4]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[4]_inst_i_3 
       (.I0(\RD_OBUF[4]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[4]_inst_i_9_n_0 ),
        .O(\RD_OBUF[4]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[4]_inst_i_4 
       (.I0(\RD_OBUF[4]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[4]_inst_i_11_n_0 ),
        .O(\RD_OBUF[4]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[4]_inst_i_5 
       (.I0(\RD_OBUF[4]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[4]_inst_i_13_n_0 ),
        .O(\RD_OBUF[4]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[4]_inst_i_6 
       (.I0(g12_b4_n_0),
        .I1(g13_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[4]_inst_i_7 
       (.I0(g14_b4_n_0),
        .I1(g15_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[4]_inst_i_8 
       (.I0(g8_b4_n_0),
        .I1(g9_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[4]_inst_i_9 
       (.I0(g10_b4_n_0),
        .I1(g11_b4_n_0),
        .O(\RD_OBUF[4]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[5]_inst 
       (.I(RD_OBUF[5]),
        .O(RD[5]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[5]_inst_i_1 
       (.I0(\RD_OBUF[5]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[5]_inst_i_3_n_0 ),
        .I2(A_IBUF[8]),
        .I3(\RD_OBUF[5]_inst_i_4_n_0 ),
        .I4(A_IBUF[7]),
        .I5(\RD_OBUF[5]_inst_i_5_n_0 ),
        .O(RD_OBUF[5]));
  MUXF7 \RD_OBUF[5]_inst_i_2 
       (.I0(g6_b5_n_0),
        .I1(g7_b5_n_0),
        .O(\RD_OBUF[5]_inst_i_2_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[5]_inst_i_3 
       (.I0(g4_b5_n_0),
        .I1(g5_b5_n_0),
        .O(\RD_OBUF[5]_inst_i_3_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[5]_inst_i_4 
       (.I0(g2_b5_n_0),
        .I1(g3_b5_n_0),
        .O(\RD_OBUF[5]_inst_i_4_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[5]_inst_i_5 
       (.I0(g0_b5_n_0),
        .I1(g1_b5_n_0),
        .O(\RD_OBUF[5]_inst_i_5_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[6]_inst 
       (.I(RD_OBUF[6]),
        .O(RD[6]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[6]_inst_i_1 
       (.I0(\RD_OBUF[6]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[6]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[6]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[6]_inst_i_5_n_0 ),
        .O(RD_OBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_10 
       (.I0(g4_b6_n_0),
        .I1(g5_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_11 
       (.I0(g6_b6_n_0),
        .I1(g7_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_12 
       (.I0(g0_b6_n_0),
        .I1(g1_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_13 
       (.I0(g2_b6_n_0),
        .I1(g3_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[6]_inst_i_2 
       (.I0(\RD_OBUF[6]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[6]_inst_i_7_n_0 ),
        .O(\RD_OBUF[6]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[6]_inst_i_3 
       (.I0(\RD_OBUF[6]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[6]_inst_i_9_n_0 ),
        .O(\RD_OBUF[6]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[6]_inst_i_4 
       (.I0(\RD_OBUF[6]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[6]_inst_i_11_n_0 ),
        .O(\RD_OBUF[6]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[6]_inst_i_5 
       (.I0(\RD_OBUF[6]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[6]_inst_i_13_n_0 ),
        .O(\RD_OBUF[6]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[6]_inst_i_6 
       (.I0(g12_b6_n_0),
        .I1(g13_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_7 
       (.I0(g14_b6_n_0),
        .I1(g15_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_8 
       (.I0(g8_b6_n_0),
        .I1(g9_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[6]_inst_i_9 
       (.I0(g10_b6_n_0),
        .I1(g11_b6_n_0),
        .O(\RD_OBUF[6]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[7]_inst 
       (.I(RD_OBUF[7]),
        .O(RD[7]));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[7]_inst_i_1 
       (.I0(\RD_OBUF[7]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[7]_inst_i_3_n_0 ),
        .I2(A_IBUF[9]),
        .I3(\RD_OBUF[7]_inst_i_4_n_0 ),
        .I4(A_IBUF[8]),
        .I5(\RD_OBUF[7]_inst_i_5_n_0 ),
        .O(RD_OBUF[7]));
  MUXF7 \RD_OBUF[7]_inst_i_10 
       (.I0(g4_b7_n_0),
        .I1(g5_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_10_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[7]_inst_i_11 
       (.I0(g6_b7_n_0),
        .I1(g7_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_11_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[7]_inst_i_12 
       (.I0(g0_b7_n_0),
        .I1(g1_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_12_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[7]_inst_i_13 
       (.I0(g2_b7_n_0),
        .I1(g3_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_13_n_0 ),
        .S(A_IBUF[6]));
  MUXF8 \RD_OBUF[7]_inst_i_2 
       (.I0(\RD_OBUF[7]_inst_i_6_n_0 ),
        .I1(\RD_OBUF[7]_inst_i_7_n_0 ),
        .O(\RD_OBUF[7]_inst_i_2_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[7]_inst_i_3 
       (.I0(\RD_OBUF[7]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[7]_inst_i_9_n_0 ),
        .O(\RD_OBUF[7]_inst_i_3_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[7]_inst_i_4 
       (.I0(\RD_OBUF[7]_inst_i_10_n_0 ),
        .I1(\RD_OBUF[7]_inst_i_11_n_0 ),
        .O(\RD_OBUF[7]_inst_i_4_n_0 ),
        .S(A_IBUF[7]));
  MUXF8 \RD_OBUF[7]_inst_i_5 
       (.I0(\RD_OBUF[7]_inst_i_12_n_0 ),
        .I1(\RD_OBUF[7]_inst_i_13_n_0 ),
        .O(\RD_OBUF[7]_inst_i_5_n_0 ),
        .S(A_IBUF[7]));
  MUXF7 \RD_OBUF[7]_inst_i_6 
       (.I0(g12_b7_n_0),
        .I1(g13_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_6_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[7]_inst_i_7 
       (.I0(g14_b7_n_0),
        .I1(g15_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_7_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[7]_inst_i_8 
       (.I0(g8_b7_n_0),
        .I1(g9_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_8_n_0 ),
        .S(A_IBUF[6]));
  MUXF7 \RD_OBUF[7]_inst_i_9 
       (.I0(g10_b7_n_0),
        .I1(g11_b7_n_0),
        .O(\RD_OBUF[7]_inst_i_9_n_0 ),
        .S(A_IBUF[6]));
  OBUF \RD_OBUF[8]_inst 
       (.I(RD_OBUF[8]),
        .O(RD[8]));
  MUXF7 \RD_OBUF[8]_inst_i_1 
       (.I0(\RD_OBUF[8]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[8]_inst_i_3_n_0 ),
        .O(RD_OBUF[8]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_10 
       (.I0(g11_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_11 
       (.I0(g9_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[8]_inst_i_2 
       (.I0(\RD_OBUF[8]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[8]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[8]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[8]_inst_i_7_n_0 ),
        .O(\RD_OBUF[8]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[8]_inst_i_3 
       (.I0(\RD_OBUF[8]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[8]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[8]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[8]_inst_i_11_n_0 ),
        .O(\RD_OBUF[8]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_4 
       (.I0(g7_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_5 
       (.I0(g5_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_6 
       (.I0(g3_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_7 
       (.I0(g1_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_8 
       (.I0(g15_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[8]_inst_i_9 
       (.I0(g13_b0__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b0__2_n_0),
        .O(\RD_OBUF[8]_inst_i_9_n_0 ));
  OBUF \RD_OBUF[9]_inst 
       (.I(RD_OBUF[9]),
        .O(RD[9]));
  MUXF7 \RD_OBUF[9]_inst_i_1 
       (.I0(\RD_OBUF[9]_inst_i_2_n_0 ),
        .I1(\RD_OBUF[9]_inst_i_3_n_0 ),
        .O(RD_OBUF[9]),
        .S(\RD_OBUF[15]_inst_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_10 
       (.I0(g11_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g10_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_11 
       (.I0(g9_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g8_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[9]_inst_i_2 
       (.I0(\RD_OBUF[9]_inst_i_4_n_0 ),
        .I1(\RD_OBUF[9]_inst_i_5_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[9]_inst_i_6_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[9]_inst_i_7_n_0 ),
        .O(\RD_OBUF[9]_inst_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hAFA0CFCFAFA0C0C0)) 
    \RD_OBUF[9]_inst_i_3 
       (.I0(\RD_OBUF[9]_inst_i_8_n_0 ),
        .I1(\RD_OBUF[9]_inst_i_9_n_0 ),
        .I2(\RD_OBUF[13]_inst_i_4_n_0 ),
        .I3(\RD_OBUF[9]_inst_i_10_n_0 ),
        .I4(\RD_OBUF[13]_inst_i_6_n_0 ),
        .I5(\RD_OBUF[9]_inst_i_11_n_0 ),
        .O(\RD_OBUF[9]_inst_i_3_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_4 
       (.I0(g7_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g6_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_5 
       (.I0(g5_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g4_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_5_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_6 
       (.I0(g3_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g2_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_7 
       (.I0(g1_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g0_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_7_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_8 
       (.I0(g15_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g14_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hEB28)) 
    \RD_OBUF[9]_inst_i_9 
       (.I0(g13_b1__2_n_0),
        .I1(\RD_OBUF[15]_inst_i_5_n_0 ),
        .I2(A_IBUF[6]),
        .I3(g12_b1__2_n_0),
        .O(\RD_OBUF[9]_inst_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hE6DD6DEE4A442CA0)) 
    g0_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b0_n_0));
  LUT6 #(
    .INIT(64'h6DD7B75D18453610)) 
    g0_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b0__0_n_0));
  LUT6 #(
    .INIT(64'hD9EE9EDD85881C50)) 
    g0_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b0__1_n_0));
  LUT6 #(
    .INIT(64'hD9EE9EDD85881C50)) 
    g0_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b0__2_n_0));
  LUT6 #(
    .INIT(64'hDDC8A05E5A92DAE9)) 
    g0_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b1_n_0));
  LUT6 #(
    .INIT(64'h557CE1079C625FE4)) 
    g0_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b1__0_n_0));
  LUT6 #(
    .INIT(64'hEEC450ADA561E5D6)) 
    g0_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b1__1_n_0));
  LUT6 #(
    .INIT(64'hEEC450ADA561E5D6)) 
    g0_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b1__2_n_0));
  LUT6 #(
    .INIT(64'hAED4B75C3F10BBE8)) 
    g0_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b2_n_0));
  LUT6 #(
    .INIT(64'h7C17693F383A7F2C)) 
    g0_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b2__0_n_0));
  LUT6 #(
    .INIT(64'h5DE87BAC3F2077D4)) 
    g0_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b2__1_n_0));
  LUT6 #(
    .INIT(64'h5DE87BAC3F2077D4)) 
    g0_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b2__2_n_0));
  LUT6 #(
    .INIT(64'h6C621CE973071BC0)) 
    g0_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b3_n_0));
  LUT6 #(
    .INIT(64'hB25417B4A8E91C2C)) 
    g0_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b3__0_n_0));
  LUT6 #(
    .INIT(64'h9C912CD6B30B27C0)) 
    g0_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b3__1_n_0));
  LUT6 #(
    .INIT(64'h9C912CD6B30B27C0)) 
    g0_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b3__2_n_0));
  LUT6 #(
    .INIT(64'h94D7C8793ED22AF5)) 
    g0_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b4_n_0));
  LUT6 #(
    .INIT(64'hC4B753C6BC363E87)) 
    g0_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b4__0_n_0));
  LUT6 #(
    .INIT(64'h68EBC4B63DE115FA)) 
    g0_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b4__1_n_0));
  LUT6 #(
    .INIT(64'h68EBC4B63DE115FA)) 
    g0_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b4__2_n_0));
  LUT6 #(
    .INIT(64'h4A9B7A9CCD259656)) 
    g0_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b5_n_0));
  LUT6 #(
    .INIT(64'h9DC23D6352D9C837)) 
    g0_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b5__0_n_0));
  LUT6 #(
    .INIT(64'h8567B56CCE1A69A9)) 
    g0_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b5__1_n_0));
  LUT6 #(
    .INIT(64'h8567B56CCE1A69A9)) 
    g0_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b5__2_n_0));
  LUT6 #(
    .INIT(64'h26AB18B01216074B)) 
    g0_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b6_n_0));
  LUT6 #(
    .INIT(64'hAF9016228823899C)) 
    g0_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b6__0_n_0));
  LUT6 #(
    .INIT(64'h1957247021290B87)) 
    g0_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b6__1_n_0));
  LUT6 #(
    .INIT(64'h1957247021290B87)) 
    g0_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b6__2_n_0));
  LUT6 #(
    .INIT(64'hAD6F7848B3FC7884)) 
    g0_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g0_b7_n_0));
  LUT6 #(
    .INIT(64'hF39D31646F2F3461)) 
    g0_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g0_b7__0_n_0));
  LUT6 #(
    .INIT(64'h5E9FB48473FCB448)) 
    g0_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g0_b7__1_n_0));
  LUT6 #(
    .INIT(64'h5E9FB48473FCB448)) 
    g0_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g0_b7__2_n_0));
  LUT6 #(
    .INIT(64'h711144702FB3B54B)) 
    g10_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b0_n_0));
  LUT6 #(
    .INIT(64'h20EA0256BE9AE1BC)) 
    g10_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b0__0_n_0));
  LUT6 #(
    .INIT(64'hB22288B01F737A87)) 
    g10_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b0__1_n_0));
  LUT6 #(
    .INIT(64'hB22288B01F737A87)) 
    g10_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b0__2_n_0));
  LUT6 #(
    .INIT(64'h44ECD8BC57DCB745)) 
    g10_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b1_n_0));
  LUT6 #(
    .INIT(64'h075557630D7F68BD)) 
    g10_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b1__0_n_0));
  LUT6 #(
    .INIT(64'h88DCE47CABEC7B8A)) 
    g10_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b1__1_n_0));
  LUT6 #(
    .INIT(64'h88DCE47CABEC7B8A)) 
    g10_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b1__2_n_0));
  LUT6 #(
    .INIT(64'h0248FF7B8A9E9599)) 
    g10_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b2_n_0));
  LUT6 #(
    .INIT(64'h0904FBFEDD0345BA)) 
    g10_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b2__0_n_0));
  LUT6 #(
    .INIT(64'h0184FFB7456D6A66)) 
    g10_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b2__1_n_0));
  LUT6 #(
    .INIT(64'h0184FFB7456D6A66)) 
    g10_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b2__2_n_0));
  LUT6 #(
    .INIT(64'hB25FE5F22A94E36E)) 
    g10_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b3_n_0));
  LUT6 #(
    .INIT(64'hE9A7E65E3C03EB4D)) 
    g10_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b3__0_n_0));
  LUT6 #(
    .INIT(64'h71AFDAF11568D39D)) 
    g10_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b3__1_n_0));
  LUT6 #(
    .INIT(64'h71AFDAF11568D39D)) 
    g10_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b3__2_n_0));
  LUT6 #(
    .INIT(64'h812975B16E1315E8)) 
    g10_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b4_n_0));
  LUT6 #(
    .INIT(64'h438826FAB8D2073C)) 
    g10_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b4__0_n_0));
  LUT6 #(
    .INIT(64'h4216BA729D232AD4)) 
    g10_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b4__1_n_0));
  LUT6 #(
    .INIT(64'h4216BA729D232AD4)) 
    g10_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b4__2_n_0));
  LUT6 #(
    .INIT(64'h83EF1CD100DC2F42)) 
    g10_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b6_n_0));
  LUT6 #(
    .INIT(64'hCF8D14B60507B81C)) 
    g10_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b6__0_n_0));
  LUT6 #(
    .INIT(64'h43DF2CE200EC1F81)) 
    g10_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b6__1_n_0));
  LUT6 #(
    .INIT(64'h43DF2CE200EC1F81)) 
    g10_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b6__2_n_0));
  LUT6 #(
    .INIT(64'h8681D6A3199EFA2E)) 
    g10_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g10_b7_n_0));
  LUT6 #(
    .INIT(64'h4C90CEF0952BFB61)) 
    g10_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g10_b7__0_n_0));
  LUT6 #(
    .INIT(64'h4942E953266DF51D)) 
    g10_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g10_b7__1_n_0));
  LUT6 #(
    .INIT(64'h4942E953266DF51D)) 
    g10_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g10_b7__2_n_0));
  LUT6 #(
    .INIT(64'h817F438670A763A7)) 
    g11_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b0_n_0));
  LUT6 #(
    .INIT(64'hC38F8C49A6E1AEC9)) 
    g11_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b0__0_n_0));
  LUT6 #(
    .INIT(64'h42BF8349B05B935B)) 
    g11_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b0__1_n_0));
  LUT6 #(
    .INIT(64'h42BF8349B05B935B)) 
    g11_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b0__2_n_0));
  LUT6 #(
    .INIT(64'h0FA162A2FC16BB27)) 
    g11_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b1_n_0));
  LUT6 #(
    .INIT(64'h1E98AE40F073FAA9)) 
    g11_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b1__0_n_0));
  LUT6 #(
    .INIT(64'h0F529151FC29771B)) 
    g11_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b1__1_n_0));
  LUT6 #(
    .INIT(64'h0F529151FC29771B)) 
    g11_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b1__2_n_0));
  LUT6 #(
    .INIT(64'h69A4C20E13C47E67)) 
    g11_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b2_n_0));
  LUT6 #(
    .INIT(64'h3649C9410C2DBAF5)) 
    g11_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b2__0_n_0));
  LUT6 #(
    .INIT(64'h9658C10D23C8BD9B)) 
    g11_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b2__1_n_0));
  LUT6 #(
    .INIT(64'h9658C10D23C8BD9B)) 
    g11_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b2__2_n_0));
  LUT6 #(
    .INIT(64'h6BE4C8FFD3C39A7C)) 
    g11_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b3_n_0));
  LUT6 #(
    .INIT(64'h3E4DD7C7CCEC5B27)) 
    g11_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b3__0_n_0));
  LUT6 #(
    .INIT(64'h97D8C4FFE3C365BC)) 
    g11_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b3__1_n_0));
  LUT6 #(
    .INIT(64'h97D8C4FFE3C365BC)) 
    g11_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b3__2_n_0));
  LUT6 #(
    .INIT(64'hF12F111BE9C48511)) 
    g11_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b4_n_0));
  LUT6 #(
    .INIT(64'hE3E981AA744D409A)) 
    g11_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b4__0_n_0));
  LUT6 #(
    .INIT(64'hF21F2227D6C84A22)) 
    g11_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b4__1_n_0));
  LUT6 #(
    .INIT(64'hF21F2227D6C84A22)) 
    g11_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b4__2_n_0));
  LUT6 #(
    .INIT(64'h8E01B286B5B8ADA1)) 
    g11_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b6_n_0));
  LUT6 #(
    .INIT(64'h5890EC21673A7698)) 
    g11_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b6__0_n_0));
  LUT6 #(
    .INIT(64'h4D0271497A745E52)) 
    g11_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b6__1_n_0));
  LUT6 #(
    .INIT(64'h4D0271497A745E52)) 
    g11_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b6__2_n_0));
  LUT6 #(
    .INIT(64'hBCF643C38AC949FD)) 
    g11_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g11_b7_n_0));
  LUT6 #(
    .INIT(64'hF6378CCC5D8417CF)) 
    g11_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g11_b7__0_n_0));
  LUT6 #(
    .INIT(64'h7CF983C345C686FE)) 
    g11_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g11_b7__1_n_0));
  LUT6 #(
    .INIT(64'h7CF983C345C686FE)) 
    g11_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g11_b7__2_n_0));
  LUT6 #(
    .INIT(64'h16859A383DD6DB22)) 
    g12_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b0_n_0));
  LUT6 #(
    .INIT(64'h0CB15B22B43FDA68)) 
    g12_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b0__0_n_0));
  LUT6 #(
    .INIT(64'h294A65343EE9E711)) 
    g12_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b0__1_n_0));
  LUT6 #(
    .INIT(64'h294A65343EE9E711)) 
    g12_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b0__2_n_0));
  LUT6 #(
    .INIT(64'h572302298FC88AFD)) 
    g12_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b1_n_0));
  LUT6 #(
    .INIT(64'h8AF80B805D1C5F87)) 
    g12_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b1__0_n_0));
  LUT6 #(
    .INIT(64'hAB1301164FC445FE)) 
    g12_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b1__1_n_0));
  LUT6 #(
    .INIT(64'hAB1301164FC445FE)) 
    g12_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b1__2_n_0));
  LUT6 #(
    .INIT(64'hB0D9DF840EDFD583)) 
    g12_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b2_n_0));
  LUT6 #(
    .INIT(64'h65A65C799D97C4F8)) 
    g12_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b2__0_n_0));
  LUT6 #(
    .INIT(64'h70E6EF480DEFEA43)) 
    g12_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b2__1_n_0));
  LUT6 #(
    .INIT(64'h70E6EF480DEFEA43)) 
    g12_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b2__2_n_0));
  LUT6 #(
    .INIT(64'hDB8B3605818C4D60)) 
    g12_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b3_n_0));
  LUT6 #(
    .INIT(64'hDDE828B14509125C)) 
    g12_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b3__0_n_0));
  LUT6 #(
    .INIT(64'hE747390A424C8E90)) 
    g12_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b3__1_n_0));
  LUT6 #(
    .INIT(64'hE747390A424C8E90)) 
    g12_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b3__2_n_0));
  LUT6 #(
    .INIT(64'h662505D880B48D8F)) 
    g12_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b4_n_0));
  LUT6 #(
    .INIT(64'h2AD1051E4603D599)) 
    g12_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b4__0_n_0));
  LUT6 #(
    .INIT(64'h991A0AE440784E4F)) 
    g12_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b4__1_n_0));
  LUT6 #(
    .INIT(64'h991A0AE440784E4F)) 
    g12_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b4__2_n_0));
  LUT6 #(
    .INIT(64'h6C30622CDF33911D)) 
    g12_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b6_n_0));
  LUT6 #(
    .INIT(64'h32522B41DAFA41AB)) 
    g12_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b6__0_n_0));
  LUT6 #(
    .INIT(64'h9C30911CEF33622E)) 
    g12_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b6__1_n_0));
  LUT6 #(
    .INIT(64'h9C30911CEF33622E)) 
    g12_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b6__2_n_0));
  LUT6 #(
    .INIT(64'hAFE460D8B3F87EC6)) 
    g12_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g12_b7_n_0));
  LUT6 #(
    .INIT(64'h7E1D25466F2EBC75)) 
    g12_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g12_b7__0_n_0));
  LUT6 #(
    .INIT(64'h5FD890E473F4BDC9)) 
    g12_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g12_b7__1_n_0));
  LUT6 #(
    .INIT(64'h5FD890E473F4BDC9)) 
    g12_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g12_b7__2_n_0));
  LUT6 #(
    .INIT(64'h2607220E3F9E0DCB)) 
    g13_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b0_n_0));
  LUT6 #(
    .INIT(64'hA891A901BD3B959C)) 
    g13_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b0__0_n_0));
  LUT6 #(
    .INIT(64'h190B110D3F6D0EC7)) 
    g13_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b0__1_n_0));
  LUT6 #(
    .INIT(64'h190B110D3F6D0EC7)) 
    g13_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b0__2_n_0));
  LUT6 #(
    .INIT(64'h35DEF8EC6CA8F127)) 
    g13_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b1_n_0));
  LUT6 #(
    .INIT(64'hA53F77653750E2E9)) 
    g13_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b1__0_n_0));
  LUT6 #(
    .INIT(64'h3AEDF4DC9C54F21B)) 
    g13_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b1__1_n_0));
  LUT6 #(
    .INIT(64'h3AEDF4DC9C54F21B)) 
    g13_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b1__2_n_0));
  LUT6 #(
    .INIT(64'h4D9EE264917A8866)) 
    g13_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b2_n_0));
  LUT6 #(
    .INIT(64'h955B6A45C32ED205)) 
    g13_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b2__0_n_0));
  LUT6 #(
    .INIT(64'h8E6DD19862B54499)) 
    g13_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b2__1_n_0));
  LUT6 #(
    .INIT(64'h8E6DD19862B54499)) 
    g13_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b2__2_n_0));
  LUT6 #(
    .INIT(64'hD787642317362D36)) 
    g13_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b3_n_0));
  LUT6 #(
    .INIT(64'hCCF9A2D08A3BB21B)) 
    g13_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b3__0_n_0));
  LUT6 #(
    .INIT(64'hEB4B98132B391E39)) 
    g13_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b3__1_n_0));
  LUT6 #(
    .INIT(64'hEB4B98132B391E39)) 
    g13_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b3__2_n_0));
  LUT6 #(
    .INIT(64'hA18919A8DFAAEAF4)) 
    g13_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b4_n_0));
  LUT6 #(
    .INIT(64'h65881728DF787E47)) 
    g13_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b4__0_n_0));
  LUT6 #(
    .INIT(64'h52462654EF55D5F8)) 
    g13_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b4__1_n_0));
  LUT6 #(
    .INIT(64'h52462654EF55D5F8)) 
    g13_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b4__2_n_0));
  LUT6 #(
    .INIT(64'h52FA49C54709721F)) 
    g13_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b6_n_0));
  LUT6 #(
    .INIT(64'h8F6614CD09D8A9E3)) 
    g13_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b6__0_n_0));
  LUT6 #(
    .INIT(64'hA1F586CA8B06B12F)) 
    g13_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b6__1_n_0));
  LUT6 #(
    .INIT(64'hA1F586CA8B06B12F)) 
    g13_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b6__2_n_0));
  LUT6 #(
    .INIT(64'h9A5D5B6B90D36EF7)) 
    g13_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g13_b7_n_0));
  LUT6 #(
    .INIT(64'h59A79BECC4A6BED7)) 
    g13_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g13_b7__0_n_0));
  LUT6 #(
    .INIT(64'h65AEA79760E39DFB)) 
    g13_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g13_b7__1_n_0));
  LUT6 #(
    .INIT(64'h65AEA79760E39DFB)) 
    g13_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g13_b7__2_n_0));
  LUT6 #(
    .INIT(64'hB80FDC4659684195)) 
    g14_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b0_n_0));
  LUT6 #(
    .INIT(64'hF1A1D075136C04CB)) 
    g14_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b0__0_n_0));
  LUT6 #(
    .INIT(64'h740FEC89A694826A)) 
    g14_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b0__1_n_0));
  LUT6 #(
    .INIT(64'h740FEC89A694826A)) 
    g14_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b0__2_n_0));
  LUT6 #(
    .INIT(64'hB46198D5A77886C6)) 
    g14_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b1_n_0));
  LUT6 #(
    .INIT(64'h62B454A76B1ECC15)) 
    g14_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b1__0_n_0));
  LUT6 #(
    .INIT(64'h789264EA5BB449C9)) 
    g14_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b1__1_n_0));
  LUT6 #(
    .INIT(64'h789264EA5BB449C9)) 
    g14_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b1__2_n_0));
  LUT6 #(
    .INIT(64'h5419EFAFAF36C87A)) 
    g14_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b2_n_0));
  LUT6 #(
    .INIT(64'h01F2FFD9FA1BD346)) 
    g14_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b2__0_n_0));
  LUT6 #(
    .INIT(64'hA826DF5F5F39C4B5)) 
    g14_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b2__1_n_0));
  LUT6 #(
    .INIT(64'hA826DF5F5F39C4B5)) 
    g14_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b2__2_n_0));
  LUT6 #(
    .INIT(64'h2D33E4713BB3397F)) 
    g14_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b3_n_0));
  LUT6 #(
    .INIT(64'hB29A62D6BEAAB3AF)) 
    g14_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b3__0_n_0));
  LUT6 #(
    .INIT(64'h1E33D8B2377336BF)) 
    g14_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b3__1_n_0));
  LUT6 #(
    .INIT(64'h1E33D8B2377336BF)) 
    g14_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b3__2_n_0));
  LUT6 #(
    .INIT(64'h283BE712A5F124AD)) 
    g14_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b4_n_0));
  LUT6 #(
    .INIT(64'hB382E85A669E2791)) 
    g14_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b4__0_n_0));
  LUT6 #(
    .INIT(64'h1437DB215AF2185E)) 
    g14_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b4__1_n_0));
  LUT6 #(
    .INIT(64'h1437DB215AF2185E)) 
    g14_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b4__2_n_0));
  LUT6 #(
    .INIT(64'h9BD5DFD3E0EDFEE0)) 
    g14_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b6_n_0));
  LUT6 #(
    .INIT(64'h5CAFDCFE67C57E74)) 
    g14_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b6__0_n_0));
  LUT6 #(
    .INIT(64'h67EAEFE3D0DEFDD0)) 
    g14_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b6__1_n_0));
  LUT6 #(
    .INIT(64'h67EAEFE3D0DEFDD0)) 
    g14_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b6__2_n_0));
  LUT6 #(
    .INIT(64'h616EEA5E0640D571)) 
    g14_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g14_b7_n_0));
  LUT6 #(
    .INIT(64'hA34DF947081442FE)) 
    g14_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g14_b7__0_n_0));
  LUT6 #(
    .INIT(64'h929DD5AD0980EAB2)) 
    g14_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g14_b7__1_n_0));
  LUT6 #(
    .INIT(64'h929DD5AD0980EAB2)) 
    g14_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g14_b7__2_n_0));
  LUT6 #(
    .INIT(64'hE884D897CA8C592C)) 
    g15_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b0_n_0));
  LUT6 #(
    .INIT(64'h7441D4E35D411369)) 
    g15_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b0__0_n_0));
  LUT6 #(
    .INIT(64'hD448E46BC54CA61C)) 
    g15_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b0__1_n_0));
  LUT6 #(
    .INIT(64'hD448E46BC54CA61C)) 
    g15_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b0__2_n_0));
  LUT6 #(
    .INIT(64'h7E74C95AC83D066B)) 
    g15_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b1_n_0));
  LUT6 #(
    .INIT(64'h3A77D14E53C38B94)) 
    g15_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b1__0_n_0));
  LUT6 #(
    .INIT(64'hBDB8C6A5C43E0997)) 
    g15_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b1__1_n_0));
  LUT6 #(
    .INIT(64'hBDB8C6A5C43E0997)) 
    g15_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b1__2_n_0));
  LUT6 #(
    .INIT(64'hA94794C6E1FCF963)) 
    g15_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b2_n_0));
  LUT6 #(
    .INIT(64'hF08DC435674FF2EC)) 
    g15_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b2__0_n_0));
  LUT6 #(
    .INIT(64'h568B68C9D2FCF693)) 
    g15_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b2__1_n_0));
  LUT6 #(
    .INIT(64'h568B68C9D2FCF693)) 
    g15_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b2__2_n_0));
  LUT6 #(
    .INIT(64'hBE158BCBD991389A)) 
    g15_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b3_n_0));
  LUT6 #(
    .INIT(64'h78B3DD8C54EAB522)) 
    g15_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b3__0_n_0));
  LUT6 #(
    .INIT(64'h7D2A47C7E6623465)) 
    g15_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b3__1_n_0));
  LUT6 #(
    .INIT(64'h7D2A47C7E6623465)) 
    g15_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b3__2_n_0));
  LUT6 #(
    .INIT(64'hC9B8AC57675EFCF5)) 
    g15_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b4_n_0));
  LUT6 #(
    .INIT(64'h574AF097A95F76F7)) 
    g15_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b4__0_n_0));
  LUT6 #(
    .INIT(64'hC6745CAB9BADFCFA)) 
    g15_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b4__1_n_0));
  LUT6 #(
    .INIT(64'hC6745CAB9BADFCFA)) 
    g15_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b4__2_n_0));
  LUT6 #(
    .INIT(64'h3945B67BAA668468)) 
    g15_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b6_n_0));
  LUT6 #(
    .INIT(64'h30ADEBB6FA054314)) 
    g15_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b6__0_n_0));
  LUT6 #(
    .INIT(64'h368A79B755994894)) 
    g15_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b6__1_n_0));
  LUT6 #(
    .INIT(64'h368A79B755994894)) 
    g15_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b6__2_n_0));
  LUT6 #(
    .INIT(64'h724DB8457F70B64A)) 
    g15_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b7_n_0));
  LUT6 #(
    .INIT(64'h29E570A53A7EE934)) 
    g15_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g15_b7__0_n_0));
  LUT6 #(
    .INIT(64'hB18E748ABFB07985)) 
    g15_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g15_b7__1_n_0));
  LUT6 #(
    .INIT(64'hB18E748ABFB07985)) 
    g15_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g15_b7__2_n_0));
  LUT2 #(
    .INIT(4'h9)) 
    g15_b7_i_1
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[0]),
        .O(sel[1]));
  LUT2 #(
    .INIT(4'h6)) 
    g15_b7_i_1__0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .O(g15_b7_i_1__0_n_0));
  LUT4 #(
    .INIT(16'h7F80)) 
    g15_b7_i_1__1
       (.I0(A_IBUF[2]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[4]),
        .O(g15_b7_i_1__1_n_0));
  LUT3 #(
    .INIT(8'h78)) 
    g15_b7_i_2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .O(g15_b7_i_2_n_0));
  LUT5 #(
    .INIT(32'h7FFF8000)) 
    g15_b7_i_2__0
       (.I0(A_IBUF[3]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[4]),
        .I4(A_IBUF[5]),
        .O(g15_b7_i_2__0_n_0));
  LUT3 #(
    .INIT(8'h1E)) 
    g15_b7_i_2__1
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[0]),
        .I2(A_IBUF[2]),
        .O(sel[2]));
  LUT4 #(
    .INIT(16'h7F80)) 
    g15_b7_i_3
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[0]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .O(g15_b7_i_3_n_0));
  LUT4 #(
    .INIT(16'h1FE0)) 
    g15_b7_i_3__0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .O(sel[3]));
  LUT5 #(
    .INIT(32'h7FFF8000)) 
    g15_b7_i_4
       (.I0(A_IBUF[2]),
        .I1(A_IBUF[0]),
        .I2(A_IBUF[1]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .O(g15_b7_i_4_n_0));
  LUT5 #(
    .INIT(32'h57FFA800)) 
    g15_b7_i_4__0
       (.I0(A_IBUF[2]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[0]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .O(sel[4]));
  LUT6 #(
    .INIT(64'h7FFFFFFF80000000)) 
    g15_b7_i_5
       (.I0(A_IBUF[3]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[0]),
        .I3(A_IBUF[2]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g15_b7_i_5_n_0));
  LUT6 #(
    .INIT(64'h57FFFFFFA8000000)) 
    g15_b7_i_5__0
       (.I0(A_IBUF[3]),
        .I1(A_IBUF[0]),
        .I2(A_IBUF[1]),
        .I3(A_IBUF[2]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(sel[5]));
  LUT6 #(
    .INIT(64'h51E9A02D5F71BDDD)) 
    g1_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b0_n_0));
  LUT6 #(
    .INIT(64'h07EC63811AFE75BF)) 
    g1_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b0__0_n_0));
  LUT6 #(
    .INIT(64'hA2D6501EAFB27EEE)) 
    g1_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b0__1_n_0));
  LUT6 #(
    .INIT(64'hA2D6501EAFB27EEE)) 
    g1_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b0__2_n_0));
  LUT6 #(
    .INIT(64'h79CD4A656993B0EA)) 
    g1_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b1_n_0));
  LUT6 #(
    .INIT(64'h35ED1AC5B4CAE724)) 
    g1_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b1__0_n_0));
  LUT6 #(
    .INIT(64'hB6CE859A966370D5)) 
    g1_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b1__1_n_0));
  LUT6 #(
    .INIT(64'hB6CE859A966370D5)) 
    g1_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b1__2_n_0));
  LUT6 #(
    .INIT(64'h34D707A747D4DCBD)) 
    g1_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b2_n_0));
  LUT6 #(
    .INIT(64'hA4B78E990C5F57F3)) 
    g1_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b2__0_n_0));
  LUT6 #(
    .INIT(64'h38EB0B5B8BE8EC7E)) 
    g1_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b2__1_n_0));
  LUT6 #(
    .INIT(64'h38EB0B5B8BE8EC7E)) 
    g1_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b2__2_n_0));
  LUT6 #(
    .INIT(64'hBEBAAAB69C55AD4F)) 
    g1_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b3_n_0));
  LUT6 #(
    .INIT(64'hFF32FE0350B7F19D)) 
    g1_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b3__0_n_0));
  LUT6 #(
    .INIT(64'h7D7555796CAA5E8F)) 
    g1_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b3__1_n_0));
  LUT6 #(
    .INIT(64'h7D7555796CAA5E8F)) 
    g1_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b3__2_n_0));
  LUT6 #(
    .INIT(64'h47FEDD39F682ADD6)) 
    g1_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b4_n_0));
  LUT6 #(
    .INIT(64'h8F5F53FAEC70F41F)) 
    g1_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b4__0_n_0));
  LUT6 #(
    .INIT(64'h8BFDEE36F9415EE9)) 
    g1_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b4__1_n_0));
  LUT6 #(
    .INIT(64'h8BFDEE36F9415EE9)) 
    g1_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b4__2_n_0));
  LUT6 #(
    .INIT(64'h94708343F29159A8)) 
    g1_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b5_n_0));
  LUT6 #(
    .INIT(64'h4236C88C6CE21768)) 
    g1_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b5__0_n_0));
  LUT6 #(
    .INIT(64'h68B04383F162A654)) 
    g1_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b5__1_n_0));
  LUT6 #(
    .INIT(64'h68B04383F162A654)) 
    g1_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b5__2_n_0));
  LUT6 #(
    .INIT(64'hC68ACA86B5982BB7)) 
    g1_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b6_n_0));
  LUT6 #(
    .INIT(64'hCD50DC41653ABE8B)) 
    g1_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b6__0_n_0));
  LUT6 #(
    .INIT(64'hC945C5497A64177B)) 
    g1_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b6__1_n_0));
  LUT6 #(
    .INIT(64'hC945C5497A64177B)) 
    g1_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b6__2_n_0));
  LUT6 #(
    .INIT(64'h1E5DD96920436757)) 
    g1_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g1_b7_n_0));
  LUT6 #(
    .INIT(64'h19B753ECA084A8DF)) 
    g1_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g1_b7__0_n_0));
  LUT6 #(
    .INIT(64'h2DAEE69610839BAB)) 
    g1_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g1_b7__1_n_0));
  LUT6 #(
    .INIT(64'h2DAEE69610839BAB)) 
    g1_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g1_b7__2_n_0));
  LUT6 #(
    .INIT(64'h12DB8364A03E3B52)) 
    g2_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b0_n_0));
  LUT6 #(
    .INIT(64'h8DA64A0DE303B82E)) 
    g2_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b0__0_n_0));
  LUT6 #(
    .INIT(64'h21E74398503D37A1)) 
    g2_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b0__1_n_0));
  LUT6 #(
    .INIT(64'h21E74398503D37A1)) 
    g2_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b0__2_n_0));
  LUT6 #(
    .INIT(64'h088D88EDB2C16C24)) 
    g2_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b1_n_0));
  LUT6 #(
    .INIT(64'h158157856CA43251)) 
    g2_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b1__0_n_0));
  LUT6 #(
    .INIT(64'h044E44DE71C29C18)) 
    g2_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b1__1_n_0));
  LUT6 #(
    .INIT(64'h044E44DE71C29C18)) 
    g2_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b1__2_n_0));
  LUT6 #(
    .INIT(64'h1CBB0431AE240FE8)) 
    g2_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b2_n_0));
  LUT6 #(
    .INIT(64'h97B202927A111F1C)) 
    g2_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b2__0_n_0));
  LUT6 #(
    .INIT(64'h2C7708325D180FD4)) 
    g2_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b2__1_n_0));
  LUT6 #(
    .INIT(64'h2C7708325D180FD4)) 
    g2_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b2__2_n_0));
  LUT6 #(
    .INIT(64'hE85114527B90C563)) 
    g2_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b3_n_0));
  LUT6 #(
    .INIT(64'h70C680363C6AC2DC)) 
    g2_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b3__0_n_0));
  LUT6 #(
    .INIT(64'hD4A228A1B760CA93)) 
    g2_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b3__1_n_0));
  LUT6 #(
    .INIT(64'hD4A228A1B760CA93)) 
    g2_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b3__2_n_0));
  LUT6 #(
    .INIT(64'h76386FA669ED996F)) 
    g2_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b4_n_0));
  LUT6 #(
    .INIT(64'h2B72BE5937CDD3AD)) 
    g2_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b4__0_n_0));
  LUT6 #(
    .INIT(64'hB9349F5996DE669F)) 
    g2_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b4__1_n_0));
  LUT6 #(
    .INIT(64'hB9349F5996DE669F)) 
    g2_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b4__2_n_0));
  LUT6 #(
    .INIT(64'hE7C53CFD1FCE2E5D)) 
    g2_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b5_n_0));
  LUT6 #(
    .INIT(64'h6CDD37B79D3D3997)) 
    g2_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b5__0_n_0));
  LUT6 #(
    .INIT(64'hDBCA3CFE2FCD1DAE)) 
    g2_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b5__1_n_0));
  LUT6 #(
    .INIT(64'hDBCA3CFE2FCD1DAE)) 
    g2_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b5__2_n_0));
  LUT6 #(
    .INIT(64'h7C10E32EFF23D0BD)) 
    g2_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b6_n_0));
  LUT6 #(
    .INIT(64'h3072EB49FAF847E3)) 
    g2_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b6__0_n_0));
  LUT6 #(
    .INIT(64'hBC20D31DFF13E07E)) 
    g2_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b6__1_n_0));
  LUT6 #(
    .INIT(64'hBC20D31DFF13E07E)) 
    g2_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b6__2_n_0));
  LUT6 #(
    .INIT(64'h056ECA721942D56C)) 
    g2_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g2_b7_n_0));
  LUT6 #(
    .INIT(64'h831DDA46902C437D)) 
    g2_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g2_b7__0_n_0));
  LUT6 #(
    .INIT(64'h0A9DC5B12681EA9C)) 
    g2_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g2_b7__1_n_0));
  LUT6 #(
    .INIT(64'h0A9DC5B12681EA9C)) 
    g2_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g2_b7__2_n_0));
  LUT6 #(
    .INIT(64'h9600AEC8DA6E25AD)) 
    g3_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b0_n_0));
  LUT6 #(
    .INIT(64'h48307D14DB652799)) 
    g3_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b0__0_n_0));
  LUT6 #(
    .INIT(64'h69005DC4E59D1A5E)) 
    g3_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b0__1_n_0));
  LUT6 #(
    .INIT(64'h69005DC4E59D1A5E)) 
    g3_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b0__2_n_0));
  LUT6 #(
    .INIT(64'h75FB8A90A6838CBC)) 
    g3_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b1_n_0));
  LUT6 #(
    .INIT(64'hA7FE5C02EC905713)) 
    g3_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b1__0_n_0));
  LUT6 #(
    .INIT(64'hBAF7456059434C7C)) 
    g3_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b1__1_n_0));
  LUT6 #(
    .INIT(64'hBAF7456059434C7C)) 
    g3_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b1__2_n_0));
  LUT6 #(
    .INIT(64'hB7FB6E3471A4C144)) 
    g3_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b2_n_0));
  LUT6 #(
    .INIT(64'hEFBE3A532669404D)) 
    g3_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b2__0_n_0));
  LUT6 #(
    .INIT(64'h7BF79D38B258C288)) 
    g3_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b2__1_n_0));
  LUT6 #(
    .INIT(64'h7BF79D38B258C288)) 
    g3_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b2__2_n_0));
  LUT6 #(
    .INIT(64'h66BA75CCC1BD861A)) 
    g3_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b3_n_0));
  LUT6 #(
    .INIT(64'hAF52257D47CBC912)) 
    g3_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b3__0_n_0));
  LUT6 #(
    .INIT(64'h9975BACCC27E4925)) 
    g3_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b3__1_n_0));
  LUT6 #(
    .INIT(64'h9975BACCC27E4925)) 
    g3_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b3__2_n_0));
  LUT6 #(
    .INIT(64'h0F487EECD299B22F)) 
    g3_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b4_n_0));
  LUT6 #(
    .INIT(64'h191C3F754DE2EBA1)) 
    g3_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b4__0_n_0));
  LUT6 #(
    .INIT(64'h0F84BDDCE166711F)) 
    g3_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b4__1_n_0));
  LUT6 #(
    .INIT(64'h0F84BDDCE166711F)) 
    g3_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b4__2_n_0));
  LUT6 #(
    .INIT(64'h48BBFB02E021D636)) 
    g3_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b5_n_0));
  LUT6 #(
    .INIT(64'h97C2F86862C0CA73)) 
    g3_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b5__0_n_0));
  LUT6 #(
    .INIT(64'h8477F701D012E939)) 
    g3_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b5__1_n_0));
  LUT6 #(
    .INIT(64'h8477F701D012E939)) 
    g3_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b5__2_n_0));
  LUT6 #(
    .INIT(64'h71FE4D794A47525E)) 
    g3_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b6_n_0));
  LUT6 #(
    .INIT(64'hA76F13DE98C58967)) 
    g3_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b6__0_n_0));
  LUT6 #(
    .INIT(64'hB2FD8EB6858BA1AD)) 
    g3_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b6__1_n_0));
  LUT6 #(
    .INIT(64'hB2FD8EB6858BA1AD)) 
    g3_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b6__2_n_0));
  LUT6 #(
    .INIT(64'h32F7F1453F71E45C)) 
    g3_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g3_b7_n_0));
  LUT6 #(
    .INIT(64'hAEA760ED3ABE6157)) 
    g3_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g3_b7__0_n_0));
  LUT6 #(
    .INIT(64'h31FBF28A3FB2D8AC)) 
    g3_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g3_b7__1_n_0));
  LUT6 #(
    .INIT(64'h31FBF28A3FB2D8AC)) 
    g3_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g3_b7__2_n_0));
  LUT6 #(
    .INIT(64'h6FC356C840E14C9A)) 
    g4_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b0_n_0));
  LUT6 #(
    .INIT(64'hBCDC0D7406C49552)) 
    g4_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b0__0_n_0));
  LUT6 #(
    .INIT(64'h9FC3A9C480D28C65)) 
    g4_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b0__1_n_0));
  LUT6 #(
    .INIT(64'h9FC3A9C480D28C65)) 
    g4_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b0__2_n_0));
  LUT6 #(
    .INIT(64'hC10C876C20C3B97C)) 
    g4_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b1_n_0));
  LUT6 #(
    .INIT(64'h41494B1DA484732F)) 
    g4_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b1__0_n_0));
  LUT6 #(
    .INIT(64'hC20C4B9C10C376BC)) 
    g4_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b1__1_n_0));
  LUT6 #(
    .INIT(64'hC20C4B9C10C376BC)) 
    g4_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b1__2_n_0));
  LUT6 #(
    .INIT(64'h9658F5D180A56FA5)) 
    g4_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b2_n_0));
  LUT6 #(
    .INIT(64'h493664FE46813ED9)) 
    g4_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b2__0_n_0));
  LUT6 #(
    .INIT(64'h69A4FAE2405A9F5A)) 
    g4_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b2__1_n_0));
  LUT6 #(
    .INIT(64'h69A4FAE2405A9F5A)) 
    g4_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b2__2_n_0));
  LUT6 #(
    .INIT(64'hD865067860E51508)) 
    g4_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b3_n_0));
  LUT6 #(
    .INIT(64'h52E50B1626C50138)) 
    g4_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b3__0_n_0));
  LUT6 #(
    .INIT(64'hE49A09B490DA2A04)) 
    g4_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b3__1_n_0));
  LUT6 #(
    .INIT(64'hE49A09B490DA2A04)) 
    g4_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b3__2_n_0));
  LUT6 #(
    .INIT(64'h64EE201C4FF709E7)) 
    g4_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b4_n_0));
  LUT6 #(
    .INIT(64'hA75521039EDF968D)) 
    g4_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b4__0_n_0));
  LUT6 #(
    .INIT(64'h98DD102C8FFB06DB)) 
    g4_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b4__1_n_0));
  LUT6 #(
    .INIT(64'h98DD102C8FFB06DB)) 
    g4_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b4__2_n_0));
  LUT6 #(
    .INIT(64'hB564856332DA69A9)) 
    g4_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b5_n_0));
  LUT6 #(
    .INIT(64'h623DC29CAD2637C8)) 
    g4_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b5__0_n_0));
  LUT6 #(
    .INIT(64'h7A984A9331E59656)) 
    g4_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b5__1_n_0));
  LUT6 #(
    .INIT(64'h7A984A9331E59656)) 
    g4_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b5__2_n_0));
  LUT6 #(
    .INIT(64'h93CF9DD320CC6EE2)) 
    g4_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b6_n_0));
  LUT6 #(
    .INIT(64'hCDADD4BE2505BE54)) 
    g4_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b6__0_n_0));
  LUT6 #(
    .INIT(64'h63CF6EE310CC9DD1)) 
    g4_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b6__1_n_0));
  LUT6 #(
    .INIT(64'h63CF6EE310CC9DD1)) 
    g4_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b6__2_n_0));
  LUT6 #(
    .INIT(64'hC3D402F46CCBEFDB)) 
    g4_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g4_b7_n_0));
  LUT6 #(
    .INIT(64'h4C4F0E07B5D4FDDE)) 
    g4_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g4_b7__0_n_0));
  LUT6 #(
    .INIT(64'hC3E801F89CC7DFE7)) 
    g4_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g4_b7__1_n_0));
  LUT6 #(
    .INIT(64'hC3E801F89CC7DFE7)) 
    g4_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g4_b7__2_n_0));
  LUT6 #(
    .INIT(64'h3644F01ED12CE302)) 
    g5_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b0_n_0));
  LUT6 #(
    .INIT(64'h2835E1634369E848)) 
    g5_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b0__0_n_0));
  LUT6 #(
    .INIT(64'h3988F02DE21CD301)) 
    g5_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b0__1_n_0));
  LUT6 #(
    .INIT(64'h3988F02DE21CD301)) 
    g5_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b0__2_n_0));
  LUT6 #(
    .INIT(64'hD832302676257E3F)) 
    g5_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b1_n_0));
  LUT6 #(
    .INIT(64'hD262A2212AF1BBF3)) 
    g5_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b1__0_n_0));
  LUT6 #(
    .INIT(64'hE4313019B91ABD3F)) 
    g5_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b1__1_n_0));
  LUT6 #(
    .INIT(64'hE4313019B91ABD3F)) 
    g5_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b1__2_n_0));
  LUT6 #(
    .INIT(64'h3B21EC4536A92507)) 
    g5_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b2_n_0));
  LUT6 #(
    .INIT(64'h3AA870D52FB0A099)) 
    g5_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b2__0_n_0));
  LUT6 #(
    .INIT(64'h3712DC8A39561A0B)) 
    g5_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b2__1_n_0));
  LUT6 #(
    .INIT(64'h3712DC8A39561A0B)) 
    g5_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b2__2_n_0));
  LUT6 #(
    .INIT(64'h480EC765729F4CEB)) 
    g5_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b3_n_0));
  LUT6 #(
    .INIT(64'h91414ADDADE397D4)) 
    g5_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b3__0_n_0));
  LUT6 #(
    .INIT(64'h840DCB9AB16F8CD7)) 
    g5_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b3__1_n_0));
  LUT6 #(
    .INIT(64'h840DCB9AB16F8CD7)) 
    g5_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b3__2_n_0));
  LUT6 #(
    .INIT(64'hC795F38EC1A1C3A7)) 
    g5_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b4_n_0));
  LUT6 #(
    .INIT(64'h4CDBED6946C8CEC9)) 
    g5_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b4__0_n_0));
  LUT6 #(
    .INIT(64'hCB6AF34DC252C35B)) 
    g5_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b4__1_n_0));
  LUT6 #(
    .INIT(64'hCB6AF34DC252C35B)) 
    g5_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b4__2_n_0));
  LUT6 #(
    .INIT(64'h6B8F7CBC0D6EA657)) 
    g5_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b5_n_0));
  LUT6 #(
    .INIT(64'hBDC93773931DE897)) 
    g5_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b5__0_n_0));
  LUT6 #(
    .INIT(64'h974FBC7C0E9D59AB)) 
    g5_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b5__1_n_0));
  LUT6 #(
    .INIT(64'h974FBC7C0E9D59AB)) 
    g5_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b5__2_n_0));
  LUT6 #(
    .INIT(64'hAD05B63AB8F68DE0)) 
    g5_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b6_n_0));
  LUT6 #(
    .INIT(64'h7099EB32F627561C)) 
    g5_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b6__0_n_0));
  LUT6 #(
    .INIT(64'h5E0A793574F94ED0)) 
    g5_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b6__1_n_0));
  LUT6 #(
    .INIT(64'h5E0A793574F94ED0)) 
    g5_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b6__2_n_0));
  LUT6 #(
    .INIT(64'hC8A712AED7DA1CE8)) 
    g5_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g5_b7_n_0));
  LUT6 #(
    .INIT(64'hD6C18F21CD7E1734)) 
    g5_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g5_b7__0_n_0));
  LUT6 #(
    .INIT(64'hC45B215DEBE52CD4)) 
    g5_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g5_b7__1_n_0));
  LUT6 #(
    .INIT(64'hC45B215DEBE52CD4)) 
    g5_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g5_b7__2_n_0));
  LUT6 #(
    .INIT(64'hEB5CF99684AAF470)) 
    g6_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b0_n_0));
  LUT6 #(
    .INIT(64'h794FF46BC7106276)) 
    g6_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b0__0_n_0));
  LUT6 #(
    .INIT(64'hD7ACF6694855F8B0)) 
    g6_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b0__1_n_0));
  LUT6 #(
    .INIT(64'hD7ACF6694855F8B0)) 
    g6_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b0__2_n_0));
  LUT6 #(
    .INIT(64'h9FB21157825091B4)) 
    g6_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b1_n_0));
  LUT6 #(
    .INIT(64'hDE3A80AF4806462B)) 
    g6_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b1__0_n_0));
  LUT6 #(
    .INIT(64'h6F7122AB41A06278)) 
    g6_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b1__1_n_0));
  LUT6 #(
    .INIT(64'h6F7122AB41A06278)) 
    g6_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b1__2_n_0));
  LUT6 #(
    .INIT(64'hBA15D401E5AD3D43)) 
    g6_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b2_n_0));
  LUT6 #(
    .INIT(64'h78A340F067D9B0BC)) 
    g6_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b2__0_n_0));
  LUT6 #(
    .INIT(64'h752AE802DA5E3E83)) 
    g6_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b2__1_n_0));
  LUT6 #(
    .INIT(64'h752AE802DA5E3E83)) 
    g6_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b2__2_n_0));
  LUT6 #(
    .INIT(64'hF4B82FB49F20D093)) 
    g6_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b3_n_0));
  LUT6 #(
    .INIT(64'h67723E1B5A38C4E2)) 
    g6_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b3__0_n_0));
  LUT6 #(
    .INIT(64'hF8741F786F10E063)) 
    g6_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b3__1_n_0));
  LUT6 #(
    .INIT(64'hF8741F786F10E063)) 
    g6_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b3__2_n_0));
  LUT6 #(
    .INIT(64'hDB0AC8C367D1FB32)) 
    g6_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b4_n_0));
  LUT6 #(
    .INIT(64'hD968D4C42CDEFA6A)) 
    g6_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b4__0_n_0));
  LUT6 #(
    .INIT(64'hE705C4C39BE2F731)) 
    g6_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b4__1_n_0));
  LUT6 #(
    .INIT(64'hE705C4C39BE2F731)) 
    g6_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b4__2_n_0));
  LUT6 #(
    .INIT(64'h183AC302E031D1A2)) 
    g6_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b5_n_0));
  LUT6 #(
    .INIT(64'h9322C84862C2C668)) 
    g6_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b5__0_n_0));
  LUT6 #(
    .INIT(64'h2435C301D032E251)) 
    g6_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b5__1_n_0));
  LUT6 #(
    .INIT(64'h2435C301D032E251)) 
    g6_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b5__2_n_0));
  LUT6 #(
    .INIT(64'h642A202C1F12011F)) 
    g6_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b6_n_0));
  LUT6 #(
    .INIT(64'hA3502301983A818B)) 
    g6_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b6__0_n_0));
  LUT6 #(
    .INIT(64'h9815101C2F21022F)) 
    g6_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b6__1_n_0));
  LUT6 #(
    .INIT(64'h9815101C2F21022F)) 
    g6_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b6__2_n_0));
  LUT6 #(
    .INIT(64'hFABB358DE6AD2B91)) 
    g6_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g6_b7_n_0));
  LUT6 #(
    .INIT(64'hFFE225B96FD13C8A)) 
    g6_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g6_b7__0_n_0));
  LUT6 #(
    .INIT(64'hF5773A4ED95E1762)) 
    g6_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g6_b7__1_n_0));
  LUT6 #(
    .INIT(64'hF5773A4ED95E1762)) 
    g6_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g6_b7__2_n_0));
  LUT6 #(
    .INIT(64'h4C93CB456252E87E)) 
    g7_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b0_n_0));
  LUT6 #(
    .INIT(64'h94D258CDA846F347)) 
    g7_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b0__0_n_0));
  LUT6 #(
    .INIT(64'h8C63C78A91A1D4BD)) 
    g7_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b0__1_n_0));
  LUT6 #(
    .INIT(64'h8C63C78A91A1D4BD)) 
    g7_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b0__2_n_0));
  LUT6 #(
    .INIT(64'h02411B37BC076BF9)) 
    g7_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b1_n_0));
  LUT6 #(
    .INIT(64'h08849AABF0B13FCE)) 
    g7_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b1__0_n_0));
  LUT6 #(
    .INIT(64'h0182273B7C0B97F6)) 
    g7_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b1__1_n_0));
  LUT6 #(
    .INIT(64'h0182273B7C0B97F6)) 
    g7_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b1__2_n_0));
  LUT6 #(
    .INIT(64'hB2D3FA35FF37D702)) 
    g7_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b2_n_0));
  LUT6 #(
    .INIT(64'hECA67AE3FAFBC878)) 
    g7_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b2__0_n_0));
  LUT6 #(
    .INIT(64'h71E3F53AFF3BEB01)) 
    g7_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b2__1_n_0));
  LUT6 #(
    .INIT(64'h71E3F53AFF3BEB01)) 
    g7_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b2__2_n_0));
  LUT6 #(
    .INIT(64'h6CF4E517BF85CDC1)) 
    g7_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b3_n_0));
  LUT6 #(
    .INIT(64'h3657E0DB7CB954DC)) 
    g7_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b3__0_n_0));
  LUT6 #(
    .INIT(64'h9CF8DA2B7F4ACEC2)) 
    g7_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b3__1_n_0));
  LUT6 #(
    .INIT(64'h9CF8DA2B7F4ACEC2)) 
    g7_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b3__2_n_0));
  LUT6 #(
    .INIT(64'h1FE9C82F6B6B2029)) 
    g7_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b4_n_0));
  LUT6 #(
    .INIT(64'h1FBCD3C1BBCC2380)) 
    g7_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b4__0_n_0));
  LUT6 #(
    .INIT(64'h2FD6C41F97971016)) 
    g7_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b4__1_n_0));
  LUT6 #(
    .INIT(64'h2FD6C41F97971016)) 
    g7_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b4__2_n_0));
  LUT6 #(
    .INIT(64'hB74404FD1FDE29C9)) 
    g7_b5
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b5_n_0));
  LUT6 #(
    .INIT(64'h683D07979D3F358C)) 
    g7_b5__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b5__0_n_0));
  LUT6 #(
    .INIT(64'h7B8808FE2FED16C6)) 
    g7_b5__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b5__1_n_0));
  LUT6 #(
    .INIT(64'h7B8808FE2FED16C6)) 
    g7_b5__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b5__2_n_0));
  LUT6 #(
    .INIT(64'hC6BA498455997B97)) 
    g7_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b6_n_0));
  LUT6 #(
    .INIT(64'hCF52144905FABCEB)) 
    g7_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b6__0_n_0));
  LUT6 #(
    .INIT(64'hC9758648AA66B76B)) 
    g7_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b6__1_n_0));
  LUT6 #(
    .INIT(64'hC9758648AA66B76B)) 
    g7_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b6__2_n_0));
  LUT6 #(
    .INIT(64'h4B080E3ED5163222)) 
    g7_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g7_b7_n_0));
  LUT6 #(
    .INIT(64'h19489B13C07BAA20)) 
    g7_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g7_b7__0_n_0));
  LUT6 #(
    .INIT(64'h87040D3DEA293111)) 
    g7_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g7_b7__1_n_0));
  LUT6 #(
    .INIT(64'h87040D3DEA293111)) 
    g7_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g7_b7__2_n_0));
  LUT6 #(
    .INIT(64'h24A6969AA4FE19D0)) 
    g8_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b0_n_0));
  LUT6 #(
    .INIT(64'hA611CD32E717142E)) 
    g8_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b0__0_n_0));
  LUT6 #(
    .INIT(64'h1859696558FD26E0)) 
    g8_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b0__1_n_0));
  LUT6 #(
    .INIT(64'h1859696558FD26E0)) 
    g8_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b0__2_n_0));
  LUT6 #(
    .INIT(64'h654043D81A8450DB)) 
    g8_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b1_n_0));
  LUT6 #(
    .INIT(64'h205C0D4E1C2185E6)) 
    g8_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b1__0_n_0));
  LUT6 #(
    .INIT(64'h9A8083E42548A0E7)) 
    g8_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b1__1_n_0));
  LUT6 #(
    .INIT(64'h9A8083E42548A0E7)) 
    g8_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b1__2_n_0));
  LUT6 #(
    .INIT(64'h0F1AFB1F907A7CB5)) 
    g8_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b2_n_0));
  LUT6 #(
    .INIT(64'h991AF9EBC32636F3)) 
    g8_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b2__0_n_0));
  LUT6 #(
    .INIT(64'h0F25F72F60B5BC7A)) 
    g8_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b2__1_n_0));
  LUT6 #(
    .INIT(64'h0F25F72F60B5BC7A)) 
    g8_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b2__2_n_0));
  LUT6 #(
    .INIT(64'h4AC706708861C57C)) 
    g8_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b3_n_0));
  LUT6 #(
    .INIT(64'h9CC50A165284435F)) 
    g8_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b3__0_n_0));
  LUT6 #(
    .INIT(64'h85CB09B04492CABC)) 
    g8_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b3__1_n_0));
  LUT6 #(
    .INIT(64'h85CB09B04492CABC)) 
    g8_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b3__2_n_0));
  LUT6 #(
    .INIT(64'hD74A1E50ECFD94C6)) 
    g8_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b4_n_0));
  LUT6 #(
    .INIT(64'hC97C183677D7C435)) 
    g8_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b4__0_n_0));
  LUT6 #(
    .INIT(64'hEB852DA0DCFE68C9)) 
    g8_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b4__1_n_0));
  LUT6 #(
    .INIT(64'hEB852DA0DCFE68C9)) 
    g8_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b4__2_n_0));
  LUT6 #(
    .INIT(64'hD954E74FEDE9F8B4)) 
    g8_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b6_n_0));
  LUT6 #(
    .INIT(64'h506FE9DD77DC7663)) 
    g8_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b6__0_n_0));
  LUT6 #(
    .INIT(64'hE6A8DB8FDED6F478)) 
    g8_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b6__1_n_0));
  LUT6 #(
    .INIT(64'hE6A8DB8FDED6F478)) 
    g8_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b6__2_n_0));
  LUT6 #(
    .INIT(64'h743B9F075E158030)) 
    g8_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g8_b7_n_0));
  LUT6 #(
    .INIT(64'hA3F2D8B918F34202)) 
    g8_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g8_b7__0_n_0));
  LUT6 #(
    .INIT(64'hB8376F0BAD2A4030)) 
    g8_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g8_b7__1_n_0));
  LUT6 #(
    .INIT(64'hB8376F0BAD2A4030)) 
    g8_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g8_b7__2_n_0));
  LUT6 #(
    .INIT(64'h7AA6F9214334D059)) 
    g9_b0
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b0_n_0));
  LUT6 #(
    .INIT(64'hBE6172E80A4B41E6)) 
    g9_b0__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b0__0_n_0));
  LUT6 #(
    .INIT(64'hB559F6128338E0A6)) 
    g9_b0__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b0__1_n_0));
  LUT6 #(
    .INIT(64'hB559F6128338E0A6)) 
    g9_b0__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b0__2_n_0));
  LUT6 #(
    .INIT(64'hA990ABE4F9BE1939)) 
    g9_b1
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b1_n_0));
  LUT6 #(
    .INIT(64'h740A7E0DF76B13AA)) 
    g9_b1__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b1__0_n_0));
  LUT6 #(
    .INIT(64'h566057D8F67D2636)) 
    g9_b1__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b1__1_n_0));
  LUT6 #(
    .INIT(64'h566057D8F67D2636)) 
    g9_b1__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b1__2_n_0));
  LUT6 #(
    .INIT(64'h7E5B097A32926544)) 
    g9_b2
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b2_n_0));
  LUT6 #(
    .INIT(64'hB9F6930EAC22205D)) 
    g9_b2__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b2__0_n_0));
  LUT6 #(
    .INIT(64'hBDA706B531619A88)) 
    g9_b2__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b2__1_n_0));
  LUT6 #(
    .INIT(64'hBDA706B531619A88)) 
    g9_b2__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b2__2_n_0));
  LUT6 #(
    .INIT(64'h44A8966AA06CBE0D)) 
    g9_b3
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b3_n_0));
  LUT6 #(
    .INIT(64'h0750CB34630579B1)) 
    g9_b3__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b3__0_n_0));
  LUT6 #(
    .INIT(64'h88546995509C7D0E)) 
    g9_b3__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b3__1_n_0));
  LUT6 #(
    .INIT(64'h88546995509C7D0E)) 
    g9_b3__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b3__2_n_0));
  LUT6 #(
    .INIT(64'hF767B6505BFC19F4)) 
    g9_b4
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b4_n_0));
  LUT6 #(
    .INIT(64'hEAFD68361F6F162F)) 
    g9_b4__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b4__0_n_0));
  LUT6 #(
    .INIT(64'hFB9B79A0A7FC26F8)) 
    g9_b4__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b4__1_n_0));
  LUT6 #(
    .INIT(64'hFB9B79A0A7FC26F8)) 
    g9_b4__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b4__2_n_0));
  LUT6 #(
    .INIT(64'h397535794A67D448)) 
    g9_b6
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b6_n_0));
  LUT6 #(
    .INIT(64'h32AF23BE9AC54174)) 
    g9_b6__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b6__0_n_0));
  LUT6 #(
    .INIT(64'h36BA3AB6859BE884)) 
    g9_b6__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b6__1_n_0));
  LUT6 #(
    .INIT(64'h36BA3AB6859BE884)) 
    g9_b6__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b6__2_n_0));
  LUT6 #(
    .INIT(64'h2728EC106A24B31F)) 
    g9_b7
       (.I0(A_IBUF[0]),
        .I1(A_IBUF[1]),
        .I2(A_IBUF[2]),
        .I3(A_IBUF[3]),
        .I4(A_IBUF[4]),
        .I5(A_IBUF[5]),
        .O(g9_b7_n_0));
  LUT6 #(
    .INIT(64'h2B1870523A41E9AB)) 
    g9_b7__0
       (.I0(A_IBUF[1]),
        .I1(A_IBUF[2]),
        .I2(A_IBUF[3]),
        .I3(A_IBUF[0]),
        .I4(g15_b7_i_1__1_n_0),
        .I5(g15_b7_i_2__0_n_0),
        .O(g9_b7__0_n_0));
  LUT6 #(
    .INIT(64'h1B14DC209518732F)) 
    g9_b7__1
       (.I0(A_IBUF[0]),
        .I1(sel[1]),
        .I2(sel[2]),
        .I3(sel[3]),
        .I4(sel[4]),
        .I5(sel[5]),
        .O(g9_b7__1_n_0));
  LUT6 #(
    .INIT(64'h1B14DC209518732F)) 
    g9_b7__2
       (.I0(A_IBUF[0]),
        .I1(g15_b7_i_1__0_n_0),
        .I2(g15_b7_i_2_n_0),
        .I3(g15_b7_i_3_n_0),
        .I4(g15_b7_i_4_n_0),
        .I5(g15_b7_i_5_n_0),
        .O(g9_b7__2_n_0));
endmodule

