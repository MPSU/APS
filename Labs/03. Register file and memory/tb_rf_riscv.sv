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
        .clk(CLK   ),
        .A1 (RA1   ),
        .A2 (RA2   ),
        .A3 (WA    ),
        .WD3(WD    ),
        .WE (WE    ),
        .RD1(RD1ref),
        .RD2(RD2ref)
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


(* STRUCTURAL_NETLIST = "yes" *)
module rf_riscv_ref
   (clk,
    A1,
    A2,
    A3,
    WD3,
    WE,
    RD1,
    RD2);
  input clk;
  input [4:0]A1;
  input [4:0]A2;
  input [4:0]A3;
  input [31:0]WD3;
  input WE;
  output [31:0]RD1;
  output [31:0]RD2;

  wire \<const0> ;
  wire [4:0]A1;
  wire [4:0]A2;
  wire [4:0]A3;
  wire [31:0]RD1;
  wire [31:0]RD11;
  wire [31:0]RD2;
  wire [31:0]RD21;
  wire [31:0]WD3;
  wire WE;
  wire clk;

  GND GND
       (.G(\<const0> ));
  (* METHODOLOGY_DRC_VIOS = "" *)
  (* RTL_RAM_BITS = "1024" *)
  (* RTL_RAM_NAME = "RAM" *)
  (* RTL_RAM_TYPE = "RAM_SDP" *)
  (* ram_addr_begin = "0" *)
  (* ram_addr_end = "31" *)
  (* ram_offset = "0" *)
  (* ram_slice_begin = "0" *)
  (* ram_slice_end = "5" *)
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000))
    RAM_reg_r1_0_31_0_5
       (.ADDRA(A1),
        .ADDRB(A1),
        .ADDRC(A1),
        .ADDRD(A3),
        .DIA(WD3[1:0]),
        .DIB(WD3[3:2]),
        .DIC(WD3[5:4]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD11[1:0]),
        .DOB(RD11[3:2]),
        .DOC(RD11[5:4]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "12" *) 
  (* ram_slice_end = "17" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r1_0_31_12_17
       (.ADDRA(A1),
        .ADDRB(A1),
        .ADDRC(A1),
        .ADDRD(A3),
        .DIA(WD3[13:12]),
        .DIB(WD3[15:14]),
        .DIC(WD3[17:16]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD11[13:12]),
        .DOB(RD11[15:14]),
        .DOC(RD11[17:16]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "18" *) 
  (* ram_slice_end = "23" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r1_0_31_18_23
       (.ADDRA(A1),
        .ADDRB(A1),
        .ADDRC(A1),
        .ADDRD(A3),
        .DIA(WD3[19:18]),
        .DIB(WD3[21:20]),
        .DIC(WD3[23:22]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD11[19:18]),
        .DOB(RD11[21:20]),
        .DOC(RD11[23:22]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "24" *) 
  (* ram_slice_end = "29" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r1_0_31_24_29
       (.ADDRA(A1),
        .ADDRB(A1),
        .ADDRC(A1),
        .ADDRD(A3),
        .DIA(WD3[25:24]),
        .DIB(WD3[27:26]),
        .DIC(WD3[29:28]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD11[25:24]),
        .DOB(RD11[27:26]),
        .DOC(RD11[29:28]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "30" *) 
  (* ram_slice_end = "31" *) 
  RAM32X1D #(
    .INIT(32'h00000000)) 
    RAM_reg_r1_0_31_30_31
       (.A0(A3[0]),
        .A1(A3[1]),
        .A2(A3[2]),
        .A3(A3[3]),
        .A4(A3[4]),
        .D(WD3[30]),
        .DPO(RD11[30]),
        .DPRA0(A1[0]),
        .DPRA1(A1[1]),
        .DPRA2(A1[2]),
        .DPRA3(A1[3]),
        .DPRA4(A1[4]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "30" *) 
  (* ram_slice_end = "31" *) 
  RAM32X1D #(
    .INIT(32'h00000000)) 
    RAM_reg_r1_0_31_30_31__0
       (.A0(A3[0]),
        .A1(A3[1]),
        .A2(A3[2]),
        .A3(A3[3]),
        .A4(A3[4]),
        .D(WD3[31]),
        .DPO(RD11[31]),
        .DPRA0(A1[0]),
        .DPRA1(A1[1]),
        .DPRA2(A1[2]),
        .DPRA3(A1[3]),
        .DPRA4(A1[4]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "6" *) 
  (* ram_slice_end = "11" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r1_0_31_6_11
       (.ADDRA(A1),
        .ADDRB(A1),
        .ADDRC(A1),
        .ADDRD(A3),
        .DIA(WD3[7:6]),
        .DIB(WD3[9:8]),
        .DIC(WD3[11:10]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD11[7:6]),
        .DOB(RD11[9:8]),
        .DOC(RD11[11:10]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "0" *) 
  (* ram_slice_end = "5" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r2_0_31_0_5
       (.ADDRA(A2),
        .ADDRB(A2),
        .ADDRC(A2),
        .ADDRD(A3),
        .DIA(WD3[1:0]),
        .DIB(WD3[3:2]),
        .DIC(WD3[5:4]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD21[1:0]),
        .DOB(RD21[3:2]),
        .DOC(RD21[5:4]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "12" *) 
  (* ram_slice_end = "17" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r2_0_31_12_17
       (.ADDRA(A2),
        .ADDRB(A2),
        .ADDRC(A2),
        .ADDRD(A3),
        .DIA(WD3[13:12]),
        .DIB(WD3[15:14]),
        .DIC(WD3[17:16]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD21[13:12]),
        .DOB(RD21[15:14]),
        .DOC(RD21[17:16]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "18" *) 
  (* ram_slice_end = "23" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r2_0_31_18_23
       (.ADDRA(A2),
        .ADDRB(A2),
        .ADDRC(A2),
        .ADDRD(A3),
        .DIA(WD3[19:18]),
        .DIB(WD3[21:20]),
        .DIC(WD3[23:22]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD21[19:18]),
        .DOB(RD21[21:20]),
        .DOC(RD21[23:22]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "24" *) 
  (* ram_slice_end = "29" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r2_0_31_24_29
       (.ADDRA(A2),
        .ADDRB(A2),
        .ADDRC(A2),
        .ADDRD(A3),
        .DIA(WD3[25:24]),
        .DIB(WD3[27:26]),
        .DIC(WD3[29:28]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD21[25:24]),
        .DOB(RD21[27:26]),
        .DOC(RD21[29:28]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "30" *) 
  (* ram_slice_end = "31" *) 
  RAM32X1D #(
    .INIT(32'h00000000)) 
    RAM_reg_r2_0_31_30_31
       (.A0(A3[0]),
        .A1(A3[1]),
        .A2(A3[2]),
        .A3(A3[3]),
        .A4(A3[4]),
        .D(WD3[30]),
        .DPO(RD21[30]),
        .DPRA0(A2[0]),
        .DPRA1(A2[1]),
        .DPRA2(A2[2]),
        .DPRA3(A2[3]),
        .DPRA4(A2[4]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "30" *) 
  (* ram_slice_end = "31" *) 
  RAM32X1D #(
    .INIT(32'h00000000)) 
    RAM_reg_r2_0_31_30_31__0
       (.A0(A3[0]),
        .A1(A3[1]),
        .A2(A3[2]),
        .A3(A3[3]),
        .A4(A3[4]),
        .D(WD3[31]),
        .DPO(RD21[31]),
        .DPRA0(A2[0]),
        .DPRA1(A2[1]),
        .DPRA2(A2[2]),
        .DPRA3(A2[3]),
        .DPRA4(A2[4]),
        .WCLK(clk),
        .WE(WE));
  (* METHODOLOGY_DRC_VIOS = "" *) 
  (* RTL_RAM_BITS = "1024" *) 
  (* RTL_RAM_NAME = "RAM" *) 
  (* RTL_RAM_TYPE = "RAM_SDP" *) 
  (* ram_addr_begin = "0" *) 
  (* ram_addr_end = "31" *) 
  (* ram_offset = "0" *) 
  (* ram_slice_begin = "6" *) 
  (* ram_slice_end = "11" *) 
  RAM32M #(
    .INIT_A(64'h0000000000000000),
    .INIT_B(64'h0000000000000000),
    .INIT_C(64'h0000000000000000),
    .INIT_D(64'h0000000000000000)) 
    RAM_reg_r2_0_31_6_11
       (.ADDRA(A2),
        .ADDRB(A2),
        .ADDRC(A2),
        .ADDRD(A3),
        .DIA(WD3[7:6]),
        .DIB(WD3[9:8]),
        .DIC(WD3[11:10]),
        .DID({\<const0> ,\<const0> }),
        .DOA(RD21[7:6]),
        .DOB(RD21[9:8]),
        .DOC(RD21[11:10]),
        .WCLK(clk),
        .WE(WE));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[0]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[0]),
        .O(RD1[0]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[10]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[10]),
        .O(RD1[10]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[11]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[11]),
        .O(RD1[11]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[12]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[12]),
        .O(RD1[12]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[13]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[13]),
        .O(RD1[13]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[14]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[14]),
        .O(RD1[14]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[15]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[15]),
        .O(RD1[15]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[16]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[16]),
        .O(RD1[16]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[17]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[17]),
        .O(RD1[17]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[18]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[18]),
        .O(RD1[18]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[19]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[19]),
        .O(RD1[19]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[1]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[1]),
        .O(RD1[1]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[20]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[20]),
        .O(RD1[20]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[21]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[21]),
        .O(RD1[21]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[22]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[22]),
        .O(RD1[22]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[23]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[23]),
        .O(RD1[23]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[24]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[24]),
        .O(RD1[24]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[25]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[25]),
        .O(RD1[25]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[26]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[26]),
        .O(RD1[26]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[27]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[27]),
        .O(RD1[27]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[28]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[28]),
        .O(RD1[28]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[29]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[29]),
        .O(RD1[29]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[2]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[2]),
        .O(RD1[2]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[30]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[30]),
        .O(RD1[30]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[31]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[31]),
        .O(RD1[31]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[3]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[3]),
        .O(RD1[3]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[4]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[4]),
        .O(RD1[4]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[5]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[5]),
        .O(RD1[5]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[6]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[6]),
        .O(RD1[6]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[7]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[7]),
        .O(RD1[7]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[8]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[8]),
        .O(RD1[8]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD1[9]_INST_0 
       (.I0(A1[2]),
        .I1(A1[1]),
        .I2(A1[4]),
        .I3(A1[3]),
        .I4(A1[0]),
        .I5(RD11[9]),
        .O(RD1[9]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[0]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[0]),
        .O(RD2[0]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[10]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[10]),
        .O(RD2[10]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[11]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[11]),
        .O(RD2[11]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[12]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[12]),
        .O(RD2[12]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[13]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[13]),
        .O(RD2[13]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[14]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[14]),
        .O(RD2[14]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[15]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[15]),
        .O(RD2[15]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[16]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[16]),
        .O(RD2[16]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[17]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[17]),
        .O(RD2[17]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[18]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[18]),
        .O(RD2[18]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[19]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[19]),
        .O(RD2[19]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[1]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[1]),
        .O(RD2[1]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[20]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[20]),
        .O(RD2[20]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[21]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[21]),
        .O(RD2[21]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[22]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[22]),
        .O(RD2[22]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[23]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[23]),
        .O(RD2[23]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[24]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[24]),
        .O(RD2[24]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[25]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[25]),
        .O(RD2[25]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[26]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[26]),
        .O(RD2[26]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[27]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[27]),
        .O(RD2[27]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[28]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[28]),
        .O(RD2[28]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[29]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[29]),
        .O(RD2[29]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[2]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[2]),
        .O(RD2[2]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[30]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[30]),
        .O(RD2[30]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[31]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[31]),
        .O(RD2[31]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[3]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[3]),
        .O(RD2[3]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[4]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[4]),
        .O(RD2[4]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[5]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[5]),
        .O(RD2[5]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[6]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[6]),
        .O(RD2[6]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[7]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[7]),
        .O(RD2[7]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[8]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[8]),
        .O(RD2[8]));
  LUT6 #(
    .INIT(64'hFFFFFFFE00000000)) 
    \RD2[9]_INST_0 
       (.I0(A2[2]),
        .I1(A2[1]),
        .I2(A2[4]),
        .I3(A2[3]),
        .I4(A2[0]),
        .I5(RD21[9]),
        .O(RD2[9]));
endmodule
