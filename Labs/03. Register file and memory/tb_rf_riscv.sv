`timescale 1ns/1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin
//
// Create Date:
// Design Name:
// Module Name:    tb_rf_riscv
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Tool Versions:
// Description: tb for RISC-V register file
//
// Dependencies:
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////

module tb_rf_riscv();

    logic        CLK;
    logic [ 4:0] RA1;
    logic [ 4:0] RA2;
    logic [ 4:0] WA;
    logic [31:0] WD;
    logic        WE;

    logic [31:0] RD1;
    logic [31:0] RD2;
    logic [31:0] RD1ref;
    logic [31:0] RD2ref;

    rf_riscv DUT(
        .clk_i         (CLK),
        .read_addr1_i  (RA1),
        .read_addr2_i  (RA2),
        .write_addr_i  (WA ),
        .write_data_i  (WD ),
        .write_enable_i(WE ),
        .read_data1_o  (RD1),
        .read_data2_o  (RD2)
    );

    rf_riscv_ref DUTref(
        .clk_i         (CLK   ),
        .read_addr1_i  (RA1   ),
        .read_addr2_i  (RA2   ),
        .write_addr_i  (WA    ),
        .write_data_i  (WD    ),
        .write_enable_i(WE    ),
        .read_data1_o  (RD1ref),
        .read_data2_o  (RD2ref)
    );

    integer i, err_count = 0;

    parameter CLK_FREQ_MHz   = 100;
    parameter CLK_SEMI_PERIOD= 1e3/CLK_FREQ_MHz/2;

    parameter address_length = 32;

    initial CLK <= 0;
    always begin
        #CLK_SEMI_PERIOD CLK = ~CLK;
        if (err_count >= 10) begin
            $display("\n\nThe test was stopped due to errors"); $stop();
        end
    end

    initial begin
      $timeformat (-9, 2, "ns");
      $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
      RA1 = 'b1;
      @(posedge CLK);
        if (32'hx !== RD1) begin
        $display("The register file should not be initialized by the $readmemh function");
        err_count = err_count + 1;
      end
      @(posedge CLK);
      DUT.rf_mem[32] = 32'd1;
      if(DUT.rf_mem[32]=== 32'd1) begin
        $display("invalid memory size");
        err_count = err_count + 1;
      end
      @(posedge CLK);
      WD <= 32'd1;
      WA <= '0;
      WE <= 1'b1;
      @(posedge CLK);
      WE  <= 'b0;
      RA1 <= 'b0;
      @(posedge CLK);
      if( RD1 !== 'b0 ) begin
        $display("time = %0t. invalid data when reading at address 0: RD1 = %h", $time, RD1);
        err_count = err_count + 1;
      end
      @(posedge CLK);
      //------initial
      CLK <= 'b0;
      RA1 <= 'b0;
      RA2 <= 'b0;
      WA  <= 'b0;
      WD  <= 'b0;
      WE  <= 'b0;
      @(posedge CLK);
      //----- reset
      for( i = 1; i < address_length; i = i + 1) begin
        @(posedge CLK);
        WA <= i;
        WD <= 'b0;
        WE <= 'b1;
      end
      @(posedge CLK);
      WA  <= 'b0;
      WD  <= 'b1;
      WE <= 'b1;
      @(posedge CLK);
      WE <= 'b0;
      RA2  <= 'b0;
      @(posedge CLK);
      if( RD2 !== 'b0 )begin
        $display("time = %0t. invalid data when reading at address 0: RD2 = %h", $time, RD2);
        err_count = err_count + 1;
      end
      @(posedge CLK);
      for( i = 1; i < address_length; i = i + 1) begin
        @(posedge CLK);
        WA <= i;
        WD <= $urandom;
        WE <= $urandom % 2;
      end
      @(posedge CLK);
      WE <= 'b0;
      for( i = 0; i < address_length; i = i + 1) begin
        @(posedge CLK);
        RA1  <= i;
        RA2  <= address_length - (i + 1);
        @(posedge CLK);
        if(RD1ref !== RD1) begin
            $display("time = %0t, address %h, RD1. Invalid data %h, correct data %h", $time, RA1, RD1, RD1ref);
            err_count = err_count + 1;
        end
        if(RD2ref !== RD2) begin
            $display("time = %0t, address %h, RD2. Invalid data %h, correct data %h", $time, RA2, RD2, RD2ref);
            err_count = err_count + 1;
        end
      end
      if( !err_count ) $display("\nregister file SUCCESS!!!\n");
      $finish();
    end
endmodule

module rf_riscv_ref(
  input  logic        clk_i,
  input  logic        write_enable_i,

  input  logic [ 4:0] write_addr_i,
  input  logic [ 4:0] read_addr1_i,
  input  logic [ 4:0] read_addr2_i,

  input  logic [31:0] write_data_i,
  output logic [31:0] read_data1_o,
  output logic [31:0] read_data2_o
);
logic [31:0] rf_mem [0:31];

`define akjsdnnaskjdnreg  $clog2(128)
`define cdyfguvhbjnmkreg  $clog2(`akjsdnnaskjdnreg)
`define qwenklfsaklasdreg $clog2(`cdyfguvhbjnmkreg)
`define asdasdhkjasdsareg (34 >> `cdyfguvhbjnmkreg)

always_ff @(posedge clk_i) begin
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][{5{1'b1}}:{3'd7,2'b00}] <= write_data_i['h1f:'h1c];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][19:{1'b1,4'h0}] <= write_data_i[42-23-:`asdasdhkjasdsareg];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][{3{1'b1}}:{1'b1,2'h0}] <= write_data_i[`akjsdnnaskjdnreg-:`asdasdhkjasdsareg];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][23:{{2{2'b10}},1'b0}] <= write_data_i[42-19-:`asdasdhkjasdsareg];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][27:{2'b11,3'b000}] <= write_data_i['h1b:'h18];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][11:{1'b1,{3{1'b0}}}] <= write_data_i[`akjsdnnaskjdnreg+`asdasdhkjasdsareg:(`akjsdnnaskjdnreg+`asdasdhkjasdsareg)-`cdyfguvhbjnmkreg];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][{2{1'b1}}:{3{1'b0}}] <= write_data_i[`akjsdnnaskjdnreg-`asdasdhkjasdsareg-:`asdasdhkjasdsareg];
    if(write_enable_i) rf_mem[write_addr_i[{1'b1,2'b0}:'hBA & 'h45]][{4{1'b1}}:4'b1100] <= write_data_i[(`akjsdnnaskjdnreg<<(`asdasdhkjasdsareg-`cdyfguvhbjnmkreg)) + (`asdasdhkjasdsareg-`cdyfguvhbjnmkreg):12]; 
end

always_comb begin
  case(read_addr1_i === ('hBA & 'h45))
  0: begin
    read_data1_o['h1f:'h1c]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][{5{1'b1}}:{3'd7,2'b00}];
    read_data1_o[42-23-:`asdasdhkjasdsareg]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][19:{1'b1,4'h0}];
    read_data1_o[`akjsdnnaskjdnreg-:`asdasdhkjasdsareg]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][{3{1'b1}}:{1'b1,2'h0}];
    read_data1_o[42-19-:`asdasdhkjasdsareg]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][23:{{2{2'b10}},1'b0}];
    read_data1_o['h1b:'h18]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][27:{2'b11,3'b000}];
    read_data1_o[`akjsdnnaskjdnreg+`asdasdhkjasdsareg:(`akjsdnnaskjdnreg+`asdasdhkjasdsareg)-`cdyfguvhbjnmkreg]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][11:8];
    read_data1_o[`akjsdnnaskjdnreg-`asdasdhkjasdsareg-:`asdasdhkjasdsareg]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][3:0];
    read_data1_o[(`akjsdnnaskjdnreg<<(`asdasdhkjasdsareg-`cdyfguvhbjnmkreg)) + (`asdasdhkjasdsareg-`cdyfguvhbjnmkreg):12 ]=rf_mem[read_addr1_i[{1'b1,2'b0}:'hBA & 'h45]][{4{1'b1}}:12];
  end
  default: read_data1_o = 'hBA & 'h45;
  endcase
end
always_comb begin
  case(read_addr2_i === ('hBA & 'h45))
  0: begin
    read_data2_o['h1f:'h1c]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][{5{1'b1}}:{3'd7,2'b00}];
    read_data2_o[42-23-:`asdasdhkjasdsareg]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][19:{1'b1,4'h0}];
    read_data2_o[`akjsdnnaskjdnreg-:`asdasdhkjasdsareg]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][{3{1'b1}}:{1'b1,2'h0}];
    read_data2_o[42-19-:`asdasdhkjasdsareg]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][23:{{2{2'b10}},1'b0}];
    read_data2_o['h1b:'h18]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][27:{2'b11,3'b000}];
    read_data2_o[`akjsdnnaskjdnreg+`asdasdhkjasdsareg:(`akjsdnnaskjdnreg+`asdasdhkjasdsareg)-`cdyfguvhbjnmkreg]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][11:8];
    read_data2_o[`akjsdnnaskjdnreg-`asdasdhkjasdsareg-:`asdasdhkjasdsareg]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][3:0];
    read_data2_o[(`akjsdnnaskjdnreg<<(`asdasdhkjasdsareg-`cdyfguvhbjnmkreg)) + (`asdasdhkjasdsareg-`cdyfguvhbjnmkreg):12 ]=rf_mem[read_addr2_i[{1'b1,2'b0}:'hBA & 'h45]][{4{1'b1}}:12];
  end
  default: read_data2_o = 'hBA & 'h45;
  endcase
end

endmodule
