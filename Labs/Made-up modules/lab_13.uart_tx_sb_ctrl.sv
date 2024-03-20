// Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// Copyright 2022-2023 Advanced Micro Devices, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2023.1 (win64) Build 3865809 Sun May  7 15:05:29 MDT 2023
// Date        : Wed Mar 20 17:54:17 2024
// Host        : a7211-12 running 64-bit major release  (build 9200)
// Command     : write_verilog {C:/Users/root/Desktop/code/verilog/brosandr.APS_refactor/Labs/Made-up
//               modules/13_obfuscate.v}
// Design      : uart_tx_sb_ctrl
// Purpose     : This is a Verilog netlist of the current design or from a specific cell of the design. The output is an
//               IEEE 1364-2001 compliant Verilog HDL file that contains netlist information obtained from the input
//               design files.
// Device      : xc7a100tcsg324-1
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module uart_tx_sb_ctrl
   (clk_i,
    rst_i,
    addr_i,
    req_i,
    write_data_i,
    write_enable_i,
    read_data_o,
    ready_o,
    tx_o);
  input clk_i;
  input rst_i;
  input [31:0]addr_i;
  input req_i;
  input [31:0]write_data_i;
  input write_enable_i;
  output [31:0]read_data_o;
  output ready_o;
  output tx_o;

  wire \<const1> ;
  wire [31:0]addr_i;
  wire [16:0]baudrate;
  wire baudrate_reg0;
  wire busy;
  wire clk_i;
  wire [7:0]data;
  wire \data[7]_i_10_n_0 ;
  wire \data[7]_i_11_n_0 ;
  wire \data[7]_i_12_n_0 ;
  wire \data[7]_i_13_n_0 ;
  wire \data[7]_i_14_n_0 ;
  wire \data[7]_i_15_n_0 ;
  wire \data[7]_i_16_n_0 ;
  wire \data[7]_i_17_n_0 ;
  wire \data[7]_i_18_n_0 ;
  wire \data[7]_i_19_n_0 ;
  wire \data[7]_i_1_n_0 ;
  wire \data[7]_i_20_n_0 ;
  wire \data[7]_i_3_n_0 ;
  wire \data[7]_i_4_n_0 ;
  wire \data[7]_i_5_n_0 ;
  wire \data[7]_i_6_n_0 ;
  wire \data[7]_i_7_n_0 ;
  wire \data[7]_i_8_n_0 ;
  wire \data[7]_i_9_n_0 ;
  wire [31:0]p_2_in__0;
  wire parity_en;
  wire parity_en_reg0;
  wire [31:0]read_data_o;
  wire \read_data_o[0]_i_2_n_0 ;
  wire \read_data_o[0]_i_3_n_0 ;
  wire \read_data_o[0]_i_4_n_0 ;
  wire \read_data_o[16]_i_2_n_0 ;
  wire \read_data_o[1]_i_2_n_0 ;
  wire \read_data_o[2]_i_2_n_0 ;
  wire \read_data_o[31]_i_3_n_0 ;
  wire \read_data_o[31]_i_4_n_0 ;
  wire \read_data_o[3]_i_2_n_0 ;
  wire \read_data_o[4]_i_2_n_0 ;
  wire \read_data_o[5]_i_2_n_0 ;
  wire \read_data_o[6]_i_2_n_0 ;
  wire \read_data_o[7]_i_2_n_0 ;
  wire read_req;
  wire ready_o;
  wire req_i;
  wire rst_i;
  wire stopbit;
  wire stopbit_i_2_n_0;
  wire stopbit_i_3_n_0;
  wire stopbit_reg0;
  wire tx_o;
  wire uart_busy;
  wire valid;
  wire valid_reg0;
  wire [31:0]write_data_i;
  wire write_enable_i;

  VCC VCC
       (.P(\<const1> ));
  LUT6 #(
    .INIT(64'h0000000000002000)) 
    \baudrate[16]_i_1 
       (.I0(\data[7]_i_7_n_0 ),
        .I1(\data[7]_i_9_n_0 ),
        .I2(addr_i[3]),
        .I3(addr_i[2]),
        .I4(addr_i[4]),
        .I5(\data[7]_i_8_n_0 ),
        .O(baudrate_reg0));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[0] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[0]),
        .Q(baudrate[0]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[10] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[10]),
        .Q(baudrate[10]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[11] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[11]),
        .Q(baudrate[11]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[12] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[12]),
        .Q(baudrate[12]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[13] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[13]),
        .Q(baudrate[13]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[14] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[14]),
        .Q(baudrate[14]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[15] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[15]),
        .Q(baudrate[15]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[16] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[16]),
        .Q(baudrate[16]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[1] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[1]),
        .Q(baudrate[1]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[2] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[2]),
        .Q(baudrate[2]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[3] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[3]),
        .Q(baudrate[3]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[4] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[4]),
        .Q(baudrate[4]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[5] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[5]),
        .Q(baudrate[5]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[6] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[6]),
        .Q(baudrate[6]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[7] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[7]),
        .Q(baudrate[7]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[8] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[8]),
        .Q(baudrate[8]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \baudrate_reg[9] 
       (.C(clk_i),
        .CE(baudrate_reg0),
        .D(write_data_i[9]),
        .Q(baudrate[9]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    busy_reg
       (.C(clk_i),
        .CE(\<const1> ),
        .D(uart_busy),
        .Q(busy),
        .R(\data[7]_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hAAAAAAABAAAAAAAA)) 
    \data[7]_i_1 
       (.I0(rst_i),
        .I1(\data[7]_i_3_n_0 ),
        .I2(\data[7]_i_4_n_0 ),
        .I3(\data[7]_i_5_n_0 ),
        .I4(\data[7]_i_6_n_0 ),
        .I5(\data[7]_i_7_n_0 ),
        .O(\data[7]_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFFE)) 
    \data[7]_i_10 
       (.I0(addr_i[7]),
        .I1(addr_i[6]),
        .I2(write_data_i[6]),
        .I3(write_data_i[28]),
        .I4(write_data_i[15]),
        .I5(write_data_i[31]),
        .O(\data[7]_i_10_n_0 ));
  LUT4 #(
    .INIT(16'hFFFE)) 
    \data[7]_i_11 
       (.I0(write_data_i[22]),
        .I1(write_data_i[2]),
        .I2(write_data_i[14]),
        .I3(write_data_i[12]),
        .O(\data[7]_i_11_n_0 ));
  LUT4 #(
    .INIT(16'h0001)) 
    \data[7]_i_12 
       (.I0(addr_i[13]),
        .I1(addr_i[11]),
        .I2(addr_i[14]),
        .I3(addr_i[8]),
        .O(\data[7]_i_12_n_0 ));
  LUT4 #(
    .INIT(16'hFFEF)) 
    \data[7]_i_13 
       (.I0(write_data_i[29]),
        .I1(write_data_i[13]),
        .I2(addr_i[5]),
        .I3(write_data_i[21]),
        .O(\data[7]_i_13_n_0 ));
  LUT4 #(
    .INIT(16'hFFFE)) 
    \data[7]_i_14 
       (.I0(write_data_i[17]),
        .I1(write_data_i[16]),
        .I2(write_data_i[19]),
        .I3(write_data_i[7]),
        .O(\data[7]_i_14_n_0 ));
  LUT4 #(
    .INIT(16'hFFFE)) 
    \data[7]_i_15 
       (.I0(write_data_i[18]),
        .I1(write_data_i[9]),
        .I2(write_data_i[25]),
        .I3(write_data_i[4]),
        .O(\data[7]_i_15_n_0 ));
  LUT4 #(
    .INIT(16'hFFFE)) 
    \data[7]_i_16 
       (.I0(write_data_i[30]),
        .I1(write_data_i[11]),
        .I2(write_data_i[24]),
        .I3(write_data_i[23]),
        .O(\data[7]_i_16_n_0 ));
  LUT4 #(
    .INIT(16'hFFFE)) 
    \data[7]_i_17 
       (.I0(write_data_i[20]),
        .I1(write_data_i[8]),
        .I2(write_data_i[1]),
        .I3(write_data_i[3]),
        .O(\data[7]_i_17_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFFE)) 
    \data[7]_i_18 
       (.I0(addr_i[29]),
        .I1(addr_i[31]),
        .I2(addr_i[30]),
        .I3(addr_i[24]),
        .I4(addr_i[27]),
        .I5(addr_i[20]),
        .O(\data[7]_i_18_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFFE)) 
    \data[7]_i_19 
       (.I0(addr_i[28]),
        .I1(addr_i[18]),
        .I2(addr_i[16]),
        .I3(addr_i[19]),
        .I4(addr_i[17]),
        .I5(addr_i[23]),
        .O(\data[7]_i_19_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000004)) 
    \data[7]_i_2 
       (.I0(addr_i[4]),
        .I1(\data[7]_i_7_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .I5(\data[7]_i_9_n_0 ),
        .O(valid_reg0));
  LUT3 #(
    .INIT(8'hFE)) 
    \data[7]_i_20 
       (.I0(addr_i[5]),
        .I1(addr_i[7]),
        .I2(addr_i[6]),
        .O(\data[7]_i_20_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFEFFFFF)) 
    \data[7]_i_3 
       (.I0(\data[7]_i_10_n_0 ),
        .I1(\data[7]_i_11_n_0 ),
        .I2(addr_i[2]),
        .I3(addr_i[4]),
        .I4(write_data_i[0]),
        .I5(addr_i[1]),
        .O(\data[7]_i_3_n_0 ));
  LUT5 #(
    .INIT(32'hFFFEFFFF)) 
    \data[7]_i_4 
       (.I0(addr_i[10]),
        .I1(addr_i[12]),
        .I2(addr_i[9]),
        .I3(addr_i[15]),
        .I4(\data[7]_i_12_n_0 ),
        .O(\data[7]_i_4_n_0 ));
  LUT4 #(
    .INIT(16'hFFFE)) 
    \data[7]_i_5 
       (.I0(\data[7]_i_13_n_0 ),
        .I1(\data[7]_i_14_n_0 ),
        .I2(\data[7]_i_15_n_0 ),
        .I3(\data[7]_i_16_n_0 ),
        .O(\data[7]_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFFE)) 
    \data[7]_i_6 
       (.I0(stopbit_i_2_n_0),
        .I1(\data[7]_i_17_n_0 ),
        .I2(write_data_i[27]),
        .I3(write_data_i[10]),
        .I4(write_data_i[26]),
        .I5(write_data_i[5]),
        .O(\data[7]_i_6_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000001)) 
    \data[7]_i_7 
       (.I0(addr_i[26]),
        .I1(addr_i[21]),
        .I2(addr_i[25]),
        .I3(addr_i[22]),
        .I4(\data[7]_i_18_n_0 ),
        .I5(\data[7]_i_19_n_0 ),
        .O(\data[7]_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFFD)) 
    \data[7]_i_8 
       (.I0(\data[7]_i_12_n_0 ),
        .I1(addr_i[15]),
        .I2(addr_i[9]),
        .I3(addr_i[12]),
        .I4(addr_i[10]),
        .I5(\data[7]_i_20_n_0 ),
        .O(\data[7]_i_8_n_0 ));
  LUT4 #(
    .INIT(16'hFFF7)) 
    \data[7]_i_9 
       (.I0(req_i),
        .I1(write_enable_i),
        .I2(addr_i[1]),
        .I3(addr_i[0]),
        .O(\data[7]_i_9_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[0] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[0]),
        .Q(data[0]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[1] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[1]),
        .Q(data[1]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[2] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[2]),
        .Q(data[2]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[3] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[3]),
        .Q(data[3]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[4] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[4]),
        .Q(data[4]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[5] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[5]),
        .Q(data[5]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[6] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[6]),
        .Q(data[6]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \data_reg[7] 
       (.C(clk_i),
        .CE(valid_reg0),
        .D(write_data_i[7]),
        .Q(data[7]),
        .R(\data[7]_i_1_n_0 ));
  LUT1 #(
    .INIT(2'h2)) 
    i_0
       (.I0(\<const1> ),
        .O(ready_o));
  LUT6 #(
    .INIT(64'h0000000000000008)) 
    parity_en_i_1
       (.I0(addr_i[4]),
        .I1(\data[7]_i_7_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .I5(\data[7]_i_9_n_0 ),
        .O(parity_en_reg0));
  
  FDRE #(
    .INIT(1'b0)) 
    parity_en_reg
       (.C(clk_i),
        .CE(parity_en_reg0),
        .D(write_data_i[0]),
        .Q(parity_en),
        .R(\data[7]_i_1_n_0 ));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[0]_i_1 
       (.I0(\read_data_o[0]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[0]),
        .O(p_2_in__0[0]));
  LUT6 #(
    .INIT(64'hFFEEFEEEEEEEFEEE)) 
    \read_data_o[0]_i_2 
       (.I0(\read_data_o[0]_i_3_n_0 ),
        .I1(\read_data_o[0]_i_4_n_0 ),
        .I2(parity_en),
        .I3(addr_i[4]),
        .I4(addr_i[2]),
        .I5(stopbit),
        .O(\read_data_o[0]_i_2_n_0 ));
  LUT5 #(
    .INIT(32'h000000E2)) 
    \read_data_o[0]_i_3 
       (.I0(data[0]),
        .I1(addr_i[3]),
        .I2(busy),
        .I3(addr_i[2]),
        .I4(addr_i[4]),
        .O(\read_data_o[0]_i_3_n_0 ));
  LUT5 #(
    .INIT(32'h0000E200)) 
    \read_data_o[0]_i_4 
       (.I0(valid),
        .I1(addr_i[3]),
        .I2(baudrate[0]),
        .I3(addr_i[2]),
        .I4(addr_i[4]),
        .O(\read_data_o[0]_i_4_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[10]_i_1 
       (.I0(baudrate[10]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[10]),
        .O(p_2_in__0[10]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[11]_i_1 
       (.I0(baudrate[11]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[11]),
        .O(p_2_in__0[11]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[12]_i_1 
       (.I0(baudrate[12]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[12]),
        .O(p_2_in__0[12]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[13]_i_1 
       (.I0(baudrate[13]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[13]),
        .O(p_2_in__0[13]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[14]_i_1 
       (.I0(baudrate[14]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[14]),
        .O(p_2_in__0[14]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[15]_i_1 
       (.I0(baudrate[15]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[15]),
        .O(p_2_in__0[15]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[16]_i_1 
       (.I0(baudrate[16]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[16]),
        .O(p_2_in__0[16]));
  LUT2 #(
    .INIT(4'h7)) 
    \read_data_o[16]_i_2 
       (.I0(addr_i[3]),
        .I1(addr_i[2]),
        .O(\read_data_o[16]_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[17]_i_1 
       (.I0(read_data_o[17]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[17]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[18]_i_1 
       (.I0(read_data_o[18]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[18]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[19]_i_1 
       (.I0(read_data_o[19]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[19]));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[1]_i_1 
       (.I0(\read_data_o[1]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[1]),
        .O(p_2_in__0[1]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[1]_i_2 
       (.I0(baudrate[1]),
        .I1(addr_i[4]),
        .I2(data[1]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[1]_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[20]_i_1 
       (.I0(read_data_o[20]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[20]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[21]_i_1 
       (.I0(read_data_o[21]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[21]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[22]_i_1 
       (.I0(read_data_o[22]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[22]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[23]_i_1 
       (.I0(read_data_o[23]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[23]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[24]_i_1 
       (.I0(read_data_o[24]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[24]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[25]_i_1 
       (.I0(read_data_o[25]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[25]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[26]_i_1 
       (.I0(read_data_o[26]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[26]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[27]_i_1 
       (.I0(read_data_o[27]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[27]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[28]_i_1 
       (.I0(read_data_o[28]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[28]));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[29]_i_1 
       (.I0(read_data_o[29]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[29]));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[2]_i_1 
       (.I0(\read_data_o[2]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[2]),
        .O(p_2_in__0[2]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[2]_i_2 
       (.I0(baudrate[2]),
        .I1(addr_i[4]),
        .I2(data[2]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[2]_i_2_n_0 ));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[30]_i_1 
       (.I0(read_data_o[30]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[30]));
  LUT2 #(
    .INIT(4'h2)) 
    \read_data_o[31]_i_1 
       (.I0(req_i),
        .I1(write_enable_i),
        .O(read_req));
  LUT4 #(
    .INIT(16'hAAA8)) 
    \read_data_o[31]_i_2 
       (.I0(read_data_o[31]),
        .I1(\read_data_o[31]_i_3_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\data[7]_i_8_n_0 ),
        .O(p_2_in__0[31]));
  LUT5 #(
    .INIT(32'hFFFFFFFE)) 
    \read_data_o[31]_i_3 
       (.I0(\data[7]_i_18_n_0 ),
        .I1(addr_i[22]),
        .I2(addr_i[25]),
        .I3(addr_i[21]),
        .I4(addr_i[26]),
        .O(\read_data_o[31]_i_3_n_0 ));
  LUT5 #(
    .INIT(32'hFFFFFFEA)) 
    \read_data_o[31]_i_4 
       (.I0(\data[7]_i_19_n_0 ),
        .I1(addr_i[3]),
        .I2(addr_i[4]),
        .I3(addr_i[0]),
        .I4(addr_i[1]),
        .O(\read_data_o[31]_i_4_n_0 ));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[3]_i_1 
       (.I0(\read_data_o[3]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[3]),
        .O(p_2_in__0[3]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[3]_i_2 
       (.I0(baudrate[3]),
        .I1(addr_i[4]),
        .I2(data[3]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[3]_i_2_n_0 ));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[4]_i_1 
       (.I0(\read_data_o[4]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[4]),
        .O(p_2_in__0[4]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[4]_i_2 
       (.I0(baudrate[4]),
        .I1(addr_i[4]),
        .I2(data[4]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[4]_i_2_n_0 ));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[5]_i_1 
       (.I0(\read_data_o[5]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[5]),
        .O(p_2_in__0[5]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[5]_i_2 
       (.I0(baudrate[5]),
        .I1(addr_i[4]),
        .I2(data[5]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[5]_i_2_n_0 ));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[6]_i_1 
       (.I0(\read_data_o[6]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[6]),
        .O(p_2_in__0[6]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[6]_i_2 
       (.I0(baudrate[6]),
        .I1(addr_i[4]),
        .I2(data[6]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[6]_i_2_n_0 ));
  LUT5 #(
    .INIT(32'hFFFE0002)) 
    \read_data_o[7]_i_1 
       (.I0(\read_data_o[7]_i_2_n_0 ),
        .I1(\data[7]_i_8_n_0 ),
        .I2(\read_data_o[31]_i_4_n_0 ),
        .I3(\read_data_o[31]_i_3_n_0 ),
        .I4(read_data_o[7]),
        .O(p_2_in__0[7]));
  LUT5 #(
    .INIT(32'hAA000030)) 
    \read_data_o[7]_i_2 
       (.I0(baudrate[7]),
        .I1(addr_i[4]),
        .I2(data[7]),
        .I3(addr_i[3]),
        .I4(addr_i[2]),
        .O(\read_data_o[7]_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[8]_i_1 
       (.I0(baudrate[8]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[8]),
        .O(p_2_in__0[8]));
  LUT6 #(
    .INIT(64'hFFFFFFF200000002)) 
    \read_data_o[9]_i_1 
       (.I0(baudrate[9]),
        .I1(\read_data_o[16]_i_2_n_0 ),
        .I2(\data[7]_i_8_n_0 ),
        .I3(\read_data_o[31]_i_4_n_0 ),
        .I4(\read_data_o[31]_i_3_n_0 ),
        .I5(read_data_o[9]),
        .O(p_2_in__0[9]));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[0] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[0]),
        .Q(read_data_o[0]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[10] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[10]),
        .Q(read_data_o[10]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[11] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[11]),
        .Q(read_data_o[11]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[12] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[12]),
        .Q(read_data_o[12]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[13] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[13]),
        .Q(read_data_o[13]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[14] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[14]),
        .Q(read_data_o[14]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[15] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[15]),
        .Q(read_data_o[15]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[16] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[16]),
        .Q(read_data_o[16]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[17] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[17]),
        .Q(read_data_o[17]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[18] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[18]),
        .Q(read_data_o[18]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[19] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[19]),
        .Q(read_data_o[19]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[1] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[1]),
        .Q(read_data_o[1]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[20] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[20]),
        .Q(read_data_o[20]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[21] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[21]),
        .Q(read_data_o[21]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[22] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[22]),
        .Q(read_data_o[22]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[23] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[23]),
        .Q(read_data_o[23]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[24] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[24]),
        .Q(read_data_o[24]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[25] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[25]),
        .Q(read_data_o[25]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[26] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[26]),
        .Q(read_data_o[26]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[27] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[27]),
        .Q(read_data_o[27]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[28] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[28]),
        .Q(read_data_o[28]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[29] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[29]),
        .Q(read_data_o[29]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[2] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[2]),
        .Q(read_data_o[2]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[30] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[30]),
        .Q(read_data_o[30]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[31] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[31]),
        .Q(read_data_o[31]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[3] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[3]),
        .Q(read_data_o[3]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[4] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[4]),
        .Q(read_data_o[4]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[5] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[5]),
        .Q(read_data_o[5]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[6] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[6]),
        .Q(read_data_o[6]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[7] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[7]),
        .Q(read_data_o[7]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[8] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[8]),
        .Q(read_data_o[8]),
        .R(\data[7]_i_1_n_0 ));
  
  FDRE #(
    .INIT(1'b0)) 
    \read_data_o_reg[9] 
       (.C(clk_i),
        .CE(read_req),
        .D(p_2_in__0[9]),
        .Q(read_data_o[9]),
        .R(\data[7]_i_1_n_0 ));
  LUT4 #(
    .INIT(16'h0002)) 
    stopbit_i_1
       (.I0(\data[7]_i_7_n_0 ),
        .I1(stopbit_i_2_n_0),
        .I2(stopbit_i_3_n_0),
        .I3(\data[7]_i_4_n_0 ),
        .O(stopbit_reg0));
  LUT4 #(
    .INIT(16'hFFF7)) 
    stopbit_i_2
       (.I0(req_i),
        .I1(write_enable_i),
        .I2(addr_i[3]),
        .I3(addr_i[0]),
        .O(stopbit_i_2_n_0));
  LUT6 #(
    .INIT(64'hFFFFFFFFFEFFFFFF)) 
    stopbit_i_3
       (.I0(addr_i[6]),
        .I1(addr_i[7]),
        .I2(addr_i[5]),
        .I3(addr_i[4]),
        .I4(addr_i[2]),
        .I5(addr_i[1]),
        .O(stopbit_i_3_n_0));
  
  FDRE #(
    .INIT(1'b0)) 
    stopbit_reg
       (.C(clk_i),
        .CE(stopbit_reg0),
        .D(write_data_i[0]),
        .Q(stopbit),
        .R(\data[7]_i_1_n_0 ));
  uart_tx tx
       (.baudrate_i(baudrate),
        .busy_o(uart_busy),
        .clk_i(clk_i),
        .parity_en_i(parity_en),
        .rst_i(rst_i),
        .stopbit_i(stopbit),
        .tx_data_i(data),
        .tx_o(tx_o),
        .tx_valid_i(valid));
  
  FDRE #(
    .INIT(1'b0)) 
    valid_reg
       (.C(clk_i),
        .CE(\<const1> ),
        .D(valid_reg0),
        .Q(valid),
        .R(\data[7]_i_1_n_0 ));
endmodule
