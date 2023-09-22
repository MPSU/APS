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

parameter ADDR_SIZE = 4096;
parameter TIME_OPERATION  = 10;
parameter STEP = 8;
    
    logic [31:0] addr;
    logic [31:0] RD;
    logic [31:0] RDref;
        
    instr_mem_ref DUTref(
    .addr_i(addr),
    .read_data_o(RDref)
    );
    
    instr_mem DUT (
    .addr_i(addr),
    .read_data_o(RD)
    );
    
    integer i, err_count = 0;
    
    assign addr = i;
    
    initial begin
        $timeformat (-9, 2, "ns");
        $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
        for (i = 0; i < ADDR_SIZE + STEP; i = i + 1 + $urandom() % STEP) begin
            #TIME_OPERATION;
            if ( RD !== RDref) begin
                $display("time = %0t, address %d. Invalid data %h, correct data %h", $time, addr, RD, RDref);
                err_count = err_count + 1;
            end
        end
        $display("Number of errors: %d", err_count);
        if( !err_count )  $display("\n instr_mem SUCCESS!!!\n");
        $finish();
    end
    
endmodule

module instr_mem_ref(
    input  [31:0] addr_i,
    output logic [31:0] read_data_o
    );

`define akjsdnnaskjdn  $clog2(128)
`define cdyfguvhbjnmk  $clog2(`akjsdnnaskjdn)
`define qwenklfsaklasd $clog2(`cdyfguvhbjnmk)
`define asdasdhkjasdsa (34 >> `cdyfguvhbjnmk)

reg [31:0] RAM [0:1023];
initial $readmemh("program.txt", RAM);

always_comb begin
  case(addr_i > {12{1'b1}})
  0: begin
    read_data_o['h1f:'h1c]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][{5{1'b1}}:{3'd7,2'b00}];
    read_data_o[42-23-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][19:{1'b1,4'h0}];
    read_data_o[`akjsdnnaskjdn-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][{3{1'b1}}:{1'b1,2'h0}];
    read_data_o[42-19-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][23:{{2{2'b10}},1'b0}];
    read_data_o['h1b:'h18]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][27:{2'b11,3'b000}];
    read_data_o[`akjsdnnaskjdn+`asdasdhkjasdsa:(`akjsdnnaskjdn+`asdasdhkjasdsa)-`cdyfguvhbjnmk]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][11:8];
    read_data_o[`akjsdnnaskjdn-`asdasdhkjasdsa-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][3:0];
    read_data_o[(`akjsdnnaskjdn<<(`asdasdhkjasdsa-`cdyfguvhbjnmk)) + (`asdasdhkjasdsa-`cdyfguvhbjnmk):12 ]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][{4{1'b1}}:12];
  end
  default: read_data_o = 'hBA & 'h45;
  endcase
end
endmodule
