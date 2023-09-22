`timescale 1 ps / 1 ps

(* STRUCTURAL_NETLIST = "yes" *)
module alu_riscv
   (alu_op_i,
    a_i,
    b_i,
    result_o,
    flag_o);
  input [4:0]alu_op_i;
  input [31:0]a_i;
  input [31:0]b_i;
  output [31:0]result_o;
  output flag_o;

  wire \<const0> ;
  wire \<const1> ;
  wire [31:0]a_i;
  wire [4:0]alu_op_i;
  wire [31:0]b_i;
  wire [31:0]data0;
  wire [31:0]data1;
  wire data3;
  wire data4;
  wire [0:0]data6;
  wire flag_o;
  wire flag_o_INST_0_i_10_n_0;
  wire flag_o_INST_0_i_10_n_1;
  wire flag_o_INST_0_i_10_n_2;
  wire flag_o_INST_0_i_10_n_3;
  wire flag_o_INST_0_i_11_n_0;
  wire flag_o_INST_0_i_12_n_0;
  wire flag_o_INST_0_i_13_n_0;
  wire flag_o_INST_0_i_14_n_0;
  wire flag_o_INST_0_i_14_n_1;
  wire flag_o_INST_0_i_14_n_2;
  wire flag_o_INST_0_i_14_n_3;
  wire flag_o_INST_0_i_15_n_0;
  wire flag_o_INST_0_i_16_n_0;
  wire flag_o_INST_0_i_17_n_0;
  wire flag_o_INST_0_i_18_n_0;
  wire flag_o_INST_0_i_19_n_0;
  wire flag_o_INST_0_i_1_n_0;
  wire flag_o_INST_0_i_20_n_0;
  wire flag_o_INST_0_i_21_n_0;
  wire flag_o_INST_0_i_22_n_0;
  wire flag_o_INST_0_i_23_n_0;
  wire flag_o_INST_0_i_23_n_1;
  wire flag_o_INST_0_i_23_n_2;
  wire flag_o_INST_0_i_23_n_3;
  wire flag_o_INST_0_i_24_n_0;
  wire flag_o_INST_0_i_25_n_0;
  wire flag_o_INST_0_i_26_n_0;
  wire flag_o_INST_0_i_27_n_0;
  wire flag_o_INST_0_i_28_n_0;
  wire flag_o_INST_0_i_28_n_1;
  wire flag_o_INST_0_i_28_n_2;
  wire flag_o_INST_0_i_28_n_3;
  wire flag_o_INST_0_i_29_n_0;
  wire flag_o_INST_0_i_2_n_0;
  wire flag_o_INST_0_i_30_n_0;
  wire flag_o_INST_0_i_31_n_0;
  wire flag_o_INST_0_i_32_n_0;
  wire flag_o_INST_0_i_33_n_0;
  wire flag_o_INST_0_i_33_n_1;
  wire flag_o_INST_0_i_33_n_2;
  wire flag_o_INST_0_i_33_n_3;
  wire flag_o_INST_0_i_34_n_0;
  wire flag_o_INST_0_i_35_n_0;
  wire flag_o_INST_0_i_36_n_0;
  wire flag_o_INST_0_i_37_n_0;
  wire flag_o_INST_0_i_38_n_0;
  wire flag_o_INST_0_i_39_n_0;
  wire flag_o_INST_0_i_3_n_1;
  wire flag_o_INST_0_i_3_n_2;
  wire flag_o_INST_0_i_3_n_3;
  wire flag_o_INST_0_i_40_n_0;
  wire flag_o_INST_0_i_41_n_0;
  wire flag_o_INST_0_i_42_n_0;
  wire flag_o_INST_0_i_43_n_0;
  wire flag_o_INST_0_i_44_n_0;
  wire flag_o_INST_0_i_45_n_0;
  wire flag_o_INST_0_i_46_n_0;
  wire flag_o_INST_0_i_47_n_0;
  wire flag_o_INST_0_i_48_n_0;
  wire flag_o_INST_0_i_49_n_0;
  wire flag_o_INST_0_i_4_n_1;
  wire flag_o_INST_0_i_4_n_2;
  wire flag_o_INST_0_i_4_n_3;
  wire flag_o_INST_0_i_50_n_0;
  wire flag_o_INST_0_i_50_n_1;
  wire flag_o_INST_0_i_50_n_2;
  wire flag_o_INST_0_i_50_n_3;
  wire flag_o_INST_0_i_51_n_0;
  wire flag_o_INST_0_i_52_n_0;
  wire flag_o_INST_0_i_53_n_0;
  wire flag_o_INST_0_i_54_n_0;
  wire flag_o_INST_0_i_55_n_0;
  wire flag_o_INST_0_i_56_n_0;
  wire flag_o_INST_0_i_57_n_0;
  wire flag_o_INST_0_i_58_n_0;
  wire flag_o_INST_0_i_59_n_0;
  wire flag_o_INST_0_i_5_n_1;
  wire flag_o_INST_0_i_5_n_2;
  wire flag_o_INST_0_i_5_n_3;
  wire flag_o_INST_0_i_60_n_0;
  wire flag_o_INST_0_i_61_n_0;
  wire flag_o_INST_0_i_62_n_0;
  wire flag_o_INST_0_i_63_n_0;
  wire flag_o_INST_0_i_64_n_0;
  wire flag_o_INST_0_i_65_n_0;
  wire flag_o_INST_0_i_66_n_0;
  wire flag_o_INST_0_i_6_n_0;
  wire flag_o_INST_0_i_6_n_1;
  wire flag_o_INST_0_i_6_n_2;
  wire flag_o_INST_0_i_6_n_3;
  wire flag_o_INST_0_i_7_n_0;
  wire flag_o_INST_0_i_8_n_0;
  wire flag_o_INST_0_i_9_n_0;
  wire [31:0]result_o;
  wire \result_o[0]_INST_0_i_10_n_0 ;
  wire \result_o[0]_INST_0_i_11_n_0 ;
  wire \result_o[0]_INST_0_i_12_n_1 ;
  wire \result_o[0]_INST_0_i_12_n_2 ;
  wire \result_o[0]_INST_0_i_12_n_3 ;
  wire \result_o[0]_INST_0_i_13_n_0 ;
  wire \result_o[0]_INST_0_i_13_n_1 ;
  wire \result_o[0]_INST_0_i_13_n_2 ;
  wire \result_o[0]_INST_0_i_13_n_3 ;
  wire \result_o[0]_INST_0_i_14_n_0 ;
  wire \result_o[0]_INST_0_i_15_n_0 ;
  wire \result_o[0]_INST_0_i_15_n_1 ;
  wire \result_o[0]_INST_0_i_15_n_2 ;
  wire \result_o[0]_INST_0_i_15_n_3 ;
  wire \result_o[0]_INST_0_i_16_n_0 ;
  wire \result_o[0]_INST_0_i_17_n_0 ;
  wire \result_o[0]_INST_0_i_18_n_0 ;
  wire \result_o[0]_INST_0_i_19_n_0 ;
  wire \result_o[0]_INST_0_i_1_n_0 ;
  wire \result_o[0]_INST_0_i_20_n_0 ;
  wire \result_o[0]_INST_0_i_21_n_0 ;
  wire \result_o[0]_INST_0_i_22_n_0 ;
  wire \result_o[0]_INST_0_i_23_n_0 ;
  wire \result_o[0]_INST_0_i_24_n_0 ;
  wire \result_o[0]_INST_0_i_24_n_1 ;
  wire \result_o[0]_INST_0_i_24_n_2 ;
  wire \result_o[0]_INST_0_i_24_n_3 ;
  wire \result_o[0]_INST_0_i_25_n_0 ;
  wire \result_o[0]_INST_0_i_26_n_0 ;
  wire \result_o[0]_INST_0_i_27_n_0 ;
  wire \result_o[0]_INST_0_i_28_n_0 ;
  wire \result_o[0]_INST_0_i_29_n_0 ;
  wire \result_o[0]_INST_0_i_2_n_0 ;
  wire \result_o[0]_INST_0_i_30_n_0 ;
  wire \result_o[0]_INST_0_i_31_n_0 ;
  wire \result_o[0]_INST_0_i_32_n_0 ;
  wire \result_o[0]_INST_0_i_33_n_0 ;
  wire \result_o[0]_INST_0_i_33_n_1 ;
  wire \result_o[0]_INST_0_i_33_n_2 ;
  wire \result_o[0]_INST_0_i_33_n_3 ;
  wire \result_o[0]_INST_0_i_34_n_0 ;
  wire \result_o[0]_INST_0_i_35_n_0 ;
  wire \result_o[0]_INST_0_i_36_n_0 ;
  wire \result_o[0]_INST_0_i_37_n_0 ;
  wire \result_o[0]_INST_0_i_38_n_0 ;
  wire \result_o[0]_INST_0_i_39_n_0 ;
  wire \result_o[0]_INST_0_i_3_n_0 ;
  wire \result_o[0]_INST_0_i_40_n_0 ;
  wire \result_o[0]_INST_0_i_41_n_0 ;
  wire \result_o[0]_INST_0_i_42_n_0 ;
  wire \result_o[0]_INST_0_i_42_n_1 ;
  wire \result_o[0]_INST_0_i_42_n_2 ;
  wire \result_o[0]_INST_0_i_42_n_3 ;
  wire \result_o[0]_INST_0_i_43_n_0 ;
  wire \result_o[0]_INST_0_i_44_n_0 ;
  wire \result_o[0]_INST_0_i_45_n_0 ;
  wire \result_o[0]_INST_0_i_46_n_0 ;
  wire \result_o[0]_INST_0_i_47_n_0 ;
  wire \result_o[0]_INST_0_i_48_n_0 ;
  wire \result_o[0]_INST_0_i_49_n_0 ;
  wire \result_o[0]_INST_0_i_50_n_0 ;
  wire \result_o[0]_INST_0_i_51_n_0 ;
  wire \result_o[0]_INST_0_i_51_n_1 ;
  wire \result_o[0]_INST_0_i_51_n_2 ;
  wire \result_o[0]_INST_0_i_51_n_3 ;
  wire \result_o[0]_INST_0_i_52_n_0 ;
  wire \result_o[0]_INST_0_i_53_n_0 ;
  wire \result_o[0]_INST_0_i_54_n_0 ;
  wire \result_o[0]_INST_0_i_55_n_0 ;
  wire \result_o[0]_INST_0_i_56_n_0 ;
  wire \result_o[0]_INST_0_i_57_n_0 ;
  wire \result_o[0]_INST_0_i_58_n_0 ;
  wire \result_o[0]_INST_0_i_59_n_0 ;
  wire \result_o[0]_INST_0_i_5_n_0 ;
  wire \result_o[0]_INST_0_i_60_n_0 ;
  wire \result_o[0]_INST_0_i_60_n_1 ;
  wire \result_o[0]_INST_0_i_60_n_2 ;
  wire \result_o[0]_INST_0_i_60_n_3 ;
  wire \result_o[0]_INST_0_i_61_n_0 ;
  wire \result_o[0]_INST_0_i_62_n_0 ;
  wire \result_o[0]_INST_0_i_63_n_0 ;
  wire \result_o[0]_INST_0_i_64_n_0 ;
  wire \result_o[0]_INST_0_i_65_n_0 ;
  wire \result_o[0]_INST_0_i_66_n_0 ;
  wire \result_o[0]_INST_0_i_67_n_0 ;
  wire \result_o[0]_INST_0_i_68_n_0 ;
  wire \result_o[0]_INST_0_i_69_n_0 ;
  wire \result_o[0]_INST_0_i_6_n_0 ;
  wire \result_o[0]_INST_0_i_70_n_0 ;
  wire \result_o[0]_INST_0_i_71_n_0 ;
  wire \result_o[0]_INST_0_i_72_n_0 ;
  wire \result_o[0]_INST_0_i_73_n_0 ;
  wire \result_o[0]_INST_0_i_74_n_0 ;
  wire \result_o[0]_INST_0_i_75_n_0 ;
  wire \result_o[0]_INST_0_i_76_n_0 ;
  wire \result_o[0]_INST_0_i_77_n_0 ;
  wire \result_o[0]_INST_0_i_78_n_0 ;
  wire \result_o[0]_INST_0_i_79_n_0 ;
  wire \result_o[0]_INST_0_i_7_n_0 ;
  wire \result_o[0]_INST_0_i_80_n_0 ;
  wire \result_o[0]_INST_0_i_81_n_0 ;
  wire \result_o[0]_INST_0_i_82_n_0 ;
  wire \result_o[0]_INST_0_i_83_n_0 ;
  wire \result_o[0]_INST_0_i_84_n_0 ;
  wire \result_o[0]_INST_0_i_8_n_0 ;
  wire \result_o[0]_INST_0_i_9_n_0 ;
  wire \result_o[10]_INST_0_i_10_n_0 ;
  wire \result_o[10]_INST_0_i_11_n_0 ;
  wire \result_o[10]_INST_0_i_12_n_0 ;
  wire \result_o[10]_INST_0_i_1_n_0 ;
  wire \result_o[10]_INST_0_i_2_n_0 ;
  wire \result_o[10]_INST_0_i_3_n_0 ;
  wire \result_o[10]_INST_0_i_4_n_0 ;
  wire \result_o[10]_INST_0_i_5_n_0 ;
  wire \result_o[10]_INST_0_i_6_n_0 ;
  wire \result_o[10]_INST_0_i_7_n_0 ;
  wire \result_o[10]_INST_0_i_8_n_0 ;
  wire \result_o[10]_INST_0_i_9_n_0 ;
  wire \result_o[11]_INST_0_i_10_n_0 ;
  wire \result_o[11]_INST_0_i_11_n_0 ;
  wire \result_o[11]_INST_0_i_11_n_1 ;
  wire \result_o[11]_INST_0_i_11_n_2 ;
  wire \result_o[11]_INST_0_i_11_n_3 ;
  wire \result_o[11]_INST_0_i_12_n_0 ;
  wire \result_o[11]_INST_0_i_13_n_0 ;
  wire \result_o[11]_INST_0_i_14_n_0 ;
  wire \result_o[11]_INST_0_i_15_n_0 ;
  wire \result_o[11]_INST_0_i_16_n_0 ;
  wire \result_o[11]_INST_0_i_17_n_0 ;
  wire \result_o[11]_INST_0_i_18_n_0 ;
  wire \result_o[11]_INST_0_i_19_n_0 ;
  wire \result_o[11]_INST_0_i_1_n_0 ;
  wire \result_o[11]_INST_0_i_20_n_0 ;
  wire \result_o[11]_INST_0_i_21_n_0 ;
  wire \result_o[11]_INST_0_i_22_n_0 ;
  wire \result_o[11]_INST_0_i_2_n_0 ;
  wire \result_o[11]_INST_0_i_3_n_0 ;
  wire \result_o[11]_INST_0_i_4_n_0 ;
  wire \result_o[11]_INST_0_i_5_n_0 ;
  wire \result_o[11]_INST_0_i_6_n_0 ;
  wire \result_o[11]_INST_0_i_7_n_0 ;
  wire \result_o[11]_INST_0_i_8_n_0 ;
  wire \result_o[11]_INST_0_i_9_n_0 ;
  wire \result_o[11]_INST_0_i_9_n_1 ;
  wire \result_o[11]_INST_0_i_9_n_2 ;
  wire \result_o[11]_INST_0_i_9_n_3 ;
  wire \result_o[12]_INST_0_i_10_n_0 ;
  wire \result_o[12]_INST_0_i_11_n_0 ;
  wire \result_o[12]_INST_0_i_12_n_0 ;
  wire \result_o[12]_INST_0_i_1_n_0 ;
  wire \result_o[12]_INST_0_i_2_n_0 ;
  wire \result_o[12]_INST_0_i_3_n_0 ;
  wire \result_o[12]_INST_0_i_4_n_0 ;
  wire \result_o[12]_INST_0_i_5_n_0 ;
  wire \result_o[12]_INST_0_i_6_n_0 ;
  wire \result_o[12]_INST_0_i_7_n_0 ;
  wire \result_o[12]_INST_0_i_8_n_0 ;
  wire \result_o[12]_INST_0_i_9_n_0 ;
  wire \result_o[13]_INST_0_i_10_n_0 ;
  wire \result_o[13]_INST_0_i_11_n_0 ;
  wire \result_o[13]_INST_0_i_12_n_0 ;
  wire \result_o[13]_INST_0_i_1_n_0 ;
  wire \result_o[13]_INST_0_i_2_n_0 ;
  wire \result_o[13]_INST_0_i_3_n_0 ;
  wire \result_o[13]_INST_0_i_4_n_0 ;
  wire \result_o[13]_INST_0_i_5_n_0 ;
  wire \result_o[13]_INST_0_i_6_n_0 ;
  wire \result_o[13]_INST_0_i_7_n_0 ;
  wire \result_o[13]_INST_0_i_8_n_0 ;
  wire \result_o[13]_INST_0_i_9_n_0 ;
  wire \result_o[14]_INST_0_i_10_n_0 ;
  wire \result_o[14]_INST_0_i_11_n_0 ;
  wire \result_o[14]_INST_0_i_12_n_0 ;
  wire \result_o[14]_INST_0_i_1_n_0 ;
  wire \result_o[14]_INST_0_i_2_n_0 ;
  wire \result_o[14]_INST_0_i_3_n_0 ;
  wire \result_o[14]_INST_0_i_4_n_0 ;
  wire \result_o[14]_INST_0_i_5_n_0 ;
  wire \result_o[14]_INST_0_i_6_n_0 ;
  wire \result_o[14]_INST_0_i_7_n_0 ;
  wire \result_o[14]_INST_0_i_8_n_0 ;
  wire \result_o[14]_INST_0_i_9_n_0 ;
  wire \result_o[15]_INST_0_i_10_n_0 ;
  wire \result_o[15]_INST_0_i_11_n_0 ;
  wire \result_o[15]_INST_0_i_11_n_1 ;
  wire \result_o[15]_INST_0_i_11_n_2 ;
  wire \result_o[15]_INST_0_i_11_n_3 ;
  wire \result_o[15]_INST_0_i_12_n_0 ;
  wire \result_o[15]_INST_0_i_13_n_0 ;
  wire \result_o[15]_INST_0_i_14_n_0 ;
  wire \result_o[15]_INST_0_i_15_n_0 ;
  wire \result_o[15]_INST_0_i_16_n_0 ;
  wire \result_o[15]_INST_0_i_17_n_0 ;
  wire \result_o[15]_INST_0_i_18_n_0 ;
  wire \result_o[15]_INST_0_i_19_n_0 ;
  wire \result_o[15]_INST_0_i_1_n_0 ;
  wire \result_o[15]_INST_0_i_20_n_0 ;
  wire \result_o[15]_INST_0_i_21_n_0 ;
  wire \result_o[15]_INST_0_i_22_n_0 ;
  wire \result_o[15]_INST_0_i_2_n_0 ;
  wire \result_o[15]_INST_0_i_3_n_0 ;
  wire \result_o[15]_INST_0_i_4_n_0 ;
  wire \result_o[15]_INST_0_i_5_n_0 ;
  wire \result_o[15]_INST_0_i_6_n_0 ;
  wire \result_o[15]_INST_0_i_7_n_0 ;
  wire \result_o[15]_INST_0_i_8_n_0 ;
  wire \result_o[15]_INST_0_i_9_n_0 ;
  wire \result_o[15]_INST_0_i_9_n_1 ;
  wire \result_o[15]_INST_0_i_9_n_2 ;
  wire \result_o[15]_INST_0_i_9_n_3 ;
  wire \result_o[16]_INST_0_i_10_n_0 ;
  wire \result_o[16]_INST_0_i_11_n_0 ;
  wire \result_o[16]_INST_0_i_1_n_0 ;
  wire \result_o[16]_INST_0_i_2_n_0 ;
  wire \result_o[16]_INST_0_i_3_n_0 ;
  wire \result_o[16]_INST_0_i_4_n_0 ;
  wire \result_o[16]_INST_0_i_5_n_0 ;
  wire \result_o[16]_INST_0_i_6_n_0 ;
  wire \result_o[16]_INST_0_i_7_n_0 ;
  wire \result_o[16]_INST_0_i_8_n_0 ;
  wire \result_o[16]_INST_0_i_9_n_0 ;
  wire \result_o[17]_INST_0_i_10_n_0 ;
  wire \result_o[17]_INST_0_i_11_n_0 ;
  wire \result_o[17]_INST_0_i_1_n_0 ;
  wire \result_o[17]_INST_0_i_2_n_0 ;
  wire \result_o[17]_INST_0_i_3_n_0 ;
  wire \result_o[17]_INST_0_i_4_n_0 ;
  wire \result_o[17]_INST_0_i_5_n_0 ;
  wire \result_o[17]_INST_0_i_6_n_0 ;
  wire \result_o[17]_INST_0_i_7_n_0 ;
  wire \result_o[17]_INST_0_i_8_n_0 ;
  wire \result_o[17]_INST_0_i_9_n_0 ;
  wire \result_o[18]_INST_0_i_10_n_0 ;
  wire \result_o[18]_INST_0_i_11_n_0 ;
  wire \result_o[18]_INST_0_i_12_n_0 ;
  wire \result_o[18]_INST_0_i_1_n_0 ;
  wire \result_o[18]_INST_0_i_2_n_0 ;
  wire \result_o[18]_INST_0_i_3_n_0 ;
  wire \result_o[18]_INST_0_i_4_n_0 ;
  wire \result_o[18]_INST_0_i_5_n_0 ;
  wire \result_o[18]_INST_0_i_6_n_0 ;
  wire \result_o[18]_INST_0_i_7_n_0 ;
  wire \result_o[18]_INST_0_i_8_n_0 ;
  wire \result_o[18]_INST_0_i_9_n_0 ;
  wire \result_o[19]_INST_0_i_10_n_0 ;
  wire \result_o[19]_INST_0_i_10_n_1 ;
  wire \result_o[19]_INST_0_i_10_n_2 ;
  wire \result_o[19]_INST_0_i_10_n_3 ;
  wire \result_o[19]_INST_0_i_11_n_0 ;
  wire \result_o[19]_INST_0_i_12_n_0 ;
  wire \result_o[19]_INST_0_i_13_n_0 ;
  wire \result_o[19]_INST_0_i_14_n_0 ;
  wire \result_o[19]_INST_0_i_15_n_0 ;
  wire \result_o[19]_INST_0_i_16_n_0 ;
  wire \result_o[19]_INST_0_i_17_n_0 ;
  wire \result_o[19]_INST_0_i_18_n_0 ;
  wire \result_o[19]_INST_0_i_19_n_0 ;
  wire \result_o[19]_INST_0_i_1_n_0 ;
  wire \result_o[19]_INST_0_i_20_n_0 ;
  wire \result_o[19]_INST_0_i_21_n_0 ;
  wire \result_o[19]_INST_0_i_22_n_0 ;
  wire \result_o[19]_INST_0_i_2_n_0 ;
  wire \result_o[19]_INST_0_i_3_n_0 ;
  wire \result_o[19]_INST_0_i_4_n_0 ;
  wire \result_o[19]_INST_0_i_5_n_0 ;
  wire \result_o[19]_INST_0_i_6_n_0 ;
  wire \result_o[19]_INST_0_i_7_n_0 ;
  wire \result_o[19]_INST_0_i_8_n_0 ;
  wire \result_o[19]_INST_0_i_9_n_0 ;
  wire \result_o[19]_INST_0_i_9_n_1 ;
  wire \result_o[19]_INST_0_i_9_n_2 ;
  wire \result_o[19]_INST_0_i_9_n_3 ;
  wire \result_o[1]_INST_0_i_1_n_0 ;
  wire \result_o[1]_INST_0_i_2_n_0 ;
  wire \result_o[1]_INST_0_i_3_n_0 ;
  wire \result_o[1]_INST_0_i_4_n_0 ;
  wire \result_o[1]_INST_0_i_5_n_0 ;
  wire \result_o[1]_INST_0_i_6_n_0 ;
  wire \result_o[1]_INST_0_i_7_n_0 ;
  wire \result_o[1]_INST_0_i_8_n_0 ;
  wire \result_o[1]_INST_0_i_9_n_0 ;
  wire \result_o[20]_INST_0_i_10_n_0 ;
  wire \result_o[20]_INST_0_i_11_n_0 ;
  wire \result_o[20]_INST_0_i_12_n_0 ;
  wire \result_o[20]_INST_0_i_1_n_0 ;
  wire \result_o[20]_INST_0_i_2_n_0 ;
  wire \result_o[20]_INST_0_i_3_n_0 ;
  wire \result_o[20]_INST_0_i_4_n_0 ;
  wire \result_o[20]_INST_0_i_5_n_0 ;
  wire \result_o[20]_INST_0_i_6_n_0 ;
  wire \result_o[20]_INST_0_i_7_n_0 ;
  wire \result_o[20]_INST_0_i_8_n_0 ;
  wire \result_o[20]_INST_0_i_9_n_0 ;
  wire \result_o[21]_INST_0_i_10_n_0 ;
  wire \result_o[21]_INST_0_i_11_n_0 ;
  wire \result_o[21]_INST_0_i_12_n_0 ;
  wire \result_o[21]_INST_0_i_1_n_0 ;
  wire \result_o[21]_INST_0_i_2_n_0 ;
  wire \result_o[21]_INST_0_i_3_n_0 ;
  wire \result_o[21]_INST_0_i_4_n_0 ;
  wire \result_o[21]_INST_0_i_5_n_0 ;
  wire \result_o[21]_INST_0_i_6_n_0 ;
  wire \result_o[21]_INST_0_i_7_n_0 ;
  wire \result_o[21]_INST_0_i_8_n_0 ;
  wire \result_o[21]_INST_0_i_9_n_0 ;
  wire \result_o[22]_INST_0_i_10_n_0 ;
  wire \result_o[22]_INST_0_i_11_n_0 ;
  wire \result_o[22]_INST_0_i_12_n_0 ;
  wire \result_o[22]_INST_0_i_1_n_0 ;
  wire \result_o[22]_INST_0_i_2_n_0 ;
  wire \result_o[22]_INST_0_i_3_n_0 ;
  wire \result_o[22]_INST_0_i_4_n_0 ;
  wire \result_o[22]_INST_0_i_5_n_0 ;
  wire \result_o[22]_INST_0_i_6_n_0 ;
  wire \result_o[22]_INST_0_i_7_n_0 ;
  wire \result_o[22]_INST_0_i_8_n_0 ;
  wire \result_o[22]_INST_0_i_9_n_0 ;
  wire \result_o[23]_INST_0_i_10_n_0 ;
  wire \result_o[23]_INST_0_i_11_n_0 ;
  wire \result_o[23]_INST_0_i_12_n_0 ;
  wire \result_o[23]_INST_0_i_13_n_0 ;
  wire \result_o[23]_INST_0_i_14_n_0 ;
  wire \result_o[23]_INST_0_i_15_n_0 ;
  wire \result_o[23]_INST_0_i_16_n_0 ;
  wire \result_o[23]_INST_0_i_17_n_0 ;
  wire \result_o[23]_INST_0_i_1_n_0 ;
  wire \result_o[23]_INST_0_i_2_n_0 ;
  wire \result_o[23]_INST_0_i_3_n_0 ;
  wire \result_o[23]_INST_0_i_4_n_0 ;
  wire \result_o[23]_INST_0_i_5_n_0 ;
  wire \result_o[23]_INST_0_i_6_n_0 ;
  wire \result_o[23]_INST_0_i_7_n_0 ;
  wire \result_o[23]_INST_0_i_8_n_0 ;
  wire \result_o[23]_INST_0_i_9_n_0 ;
  wire \result_o[23]_INST_0_i_9_n_1 ;
  wire \result_o[23]_INST_0_i_9_n_2 ;
  wire \result_o[23]_INST_0_i_9_n_3 ;
  wire \result_o[24]_INST_0_i_10_n_0 ;
  wire \result_o[24]_INST_0_i_11_n_0 ;
  wire \result_o[24]_INST_0_i_1_n_0 ;
  wire \result_o[24]_INST_0_i_2_n_0 ;
  wire \result_o[24]_INST_0_i_3_n_0 ;
  wire \result_o[24]_INST_0_i_4_n_0 ;
  wire \result_o[24]_INST_0_i_5_n_0 ;
  wire \result_o[24]_INST_0_i_6_n_0 ;
  wire \result_o[24]_INST_0_i_7_n_0 ;
  wire \result_o[24]_INST_0_i_8_n_0 ;
  wire \result_o[24]_INST_0_i_9_n_0 ;
  wire \result_o[25]_INST_0_i_10_n_0 ;
  wire \result_o[25]_INST_0_i_11_n_0 ;
  wire \result_o[25]_INST_0_i_12_n_0 ;
  wire \result_o[25]_INST_0_i_1_n_0 ;
  wire \result_o[25]_INST_0_i_2_n_0 ;
  wire \result_o[25]_INST_0_i_3_n_0 ;
  wire \result_o[25]_INST_0_i_4_n_0 ;
  wire \result_o[25]_INST_0_i_5_n_0 ;
  wire \result_o[25]_INST_0_i_6_n_0 ;
  wire \result_o[25]_INST_0_i_7_n_0 ;
  wire \result_o[25]_INST_0_i_8_n_0 ;
  wire \result_o[25]_INST_0_i_9_n_0 ;
  wire \result_o[26]_INST_0_i_10_n_0 ;
  wire \result_o[26]_INST_0_i_11_n_0 ;
  wire \result_o[26]_INST_0_i_12_n_0 ;
  wire \result_o[26]_INST_0_i_1_n_0 ;
  wire \result_o[26]_INST_0_i_2_n_0 ;
  wire \result_o[26]_INST_0_i_3_n_0 ;
  wire \result_o[26]_INST_0_i_4_n_0 ;
  wire \result_o[26]_INST_0_i_5_n_0 ;
  wire \result_o[26]_INST_0_i_6_n_0 ;
  wire \result_o[26]_INST_0_i_7_n_0 ;
  wire \result_o[26]_INST_0_i_8_n_0 ;
  wire \result_o[26]_INST_0_i_9_n_0 ;
  wire \result_o[27]_INST_0_i_10_n_0 ;
  wire \result_o[27]_INST_0_i_11_n_0 ;
  wire \result_o[27]_INST_0_i_12_n_0 ;
  wire \result_o[27]_INST_0_i_13_n_0 ;
  wire \result_o[27]_INST_0_i_14_n_0 ;
  wire \result_o[27]_INST_0_i_15_n_0 ;
  wire \result_o[27]_INST_0_i_16_n_0 ;
  wire \result_o[27]_INST_0_i_17_n_0 ;
  wire \result_o[27]_INST_0_i_18_n_0 ;
  wire \result_o[27]_INST_0_i_19_n_0 ;
  wire \result_o[27]_INST_0_i_1_n_0 ;
  wire \result_o[27]_INST_0_i_20_n_0 ;
  wire \result_o[27]_INST_0_i_21_n_0 ;
  wire \result_o[27]_INST_0_i_22_n_0 ;
  wire \result_o[27]_INST_0_i_23_n_0 ;
  wire \result_o[27]_INST_0_i_24_n_0 ;
  wire \result_o[27]_INST_0_i_25_n_0 ;
  wire \result_o[27]_INST_0_i_2_n_0 ;
  wire \result_o[27]_INST_0_i_3_n_0 ;
  wire \result_o[27]_INST_0_i_4_n_0 ;
  wire \result_o[27]_INST_0_i_4_n_1 ;
  wire \result_o[27]_INST_0_i_4_n_2 ;
  wire \result_o[27]_INST_0_i_4_n_3 ;
  wire \result_o[27]_INST_0_i_5_n_0 ;
  wire \result_o[27]_INST_0_i_6_n_0 ;
  wire \result_o[27]_INST_0_i_7_n_0 ;
  wire \result_o[27]_INST_0_i_8_n_0 ;
  wire \result_o[27]_INST_0_i_8_n_1 ;
  wire \result_o[27]_INST_0_i_8_n_2 ;
  wire \result_o[27]_INST_0_i_8_n_3 ;
  wire \result_o[27]_INST_0_i_9_n_0 ;
  wire \result_o[27]_INST_0_i_9_n_1 ;
  wire \result_o[27]_INST_0_i_9_n_2 ;
  wire \result_o[27]_INST_0_i_9_n_3 ;
  wire \result_o[28]_INST_0_i_10_n_0 ;
  wire \result_o[28]_INST_0_i_11_n_0 ;
  wire \result_o[28]_INST_0_i_12_n_0 ;
  wire \result_o[28]_INST_0_i_13_n_0 ;
  wire \result_o[28]_INST_0_i_14_n_0 ;
  wire \result_o[28]_INST_0_i_15_n_0 ;
  wire \result_o[28]_INST_0_i_1_n_0 ;
  wire \result_o[28]_INST_0_i_2_n_0 ;
  wire \result_o[28]_INST_0_i_3_n_0 ;
  wire \result_o[28]_INST_0_i_4_n_0 ;
  wire \result_o[28]_INST_0_i_5_n_1 ;
  wire \result_o[28]_INST_0_i_5_n_2 ;
  wire \result_o[28]_INST_0_i_5_n_3 ;
  wire \result_o[28]_INST_0_i_6_n_0 ;
  wire \result_o[28]_INST_0_i_7_n_0 ;
  wire \result_o[28]_INST_0_i_8_n_0 ;
  wire \result_o[28]_INST_0_i_9_n_0 ;
  wire \result_o[29]_INST_0_i_10_n_0 ;
  wire \result_o[29]_INST_0_i_1_n_0 ;
  wire \result_o[29]_INST_0_i_2_n_0 ;
  wire \result_o[29]_INST_0_i_3_n_0 ;
  wire \result_o[29]_INST_0_i_4_n_0 ;
  wire \result_o[29]_INST_0_i_5_n_0 ;
  wire \result_o[29]_INST_0_i_6_n_0 ;
  wire \result_o[29]_INST_0_i_7_n_0 ;
  wire \result_o[29]_INST_0_i_8_n_0 ;
  wire \result_o[29]_INST_0_i_9_n_0 ;
  wire \result_o[2]_INST_0_i_10_n_0 ;
  wire \result_o[2]_INST_0_i_11_n_0 ;
  wire \result_o[2]_INST_0_i_12_n_0 ;
  wire \result_o[2]_INST_0_i_13_n_0 ;
  wire \result_o[2]_INST_0_i_14_n_0 ;
  wire \result_o[2]_INST_0_i_1_n_0 ;
  wire \result_o[2]_INST_0_i_2_n_0 ;
  wire \result_o[2]_INST_0_i_3_n_0 ;
  wire \result_o[2]_INST_0_i_4_n_0 ;
  wire \result_o[2]_INST_0_i_5_n_0 ;
  wire \result_o[2]_INST_0_i_6_n_0 ;
  wire \result_o[2]_INST_0_i_7_n_0 ;
  wire \result_o[2]_INST_0_i_8_n_0 ;
  wire \result_o[2]_INST_0_i_9_n_0 ;
  wire \result_o[30]_INST_0_i_10_n_0 ;
  wire \result_o[30]_INST_0_i_11_n_0 ;
  wire \result_o[30]_INST_0_i_12_n_0 ;
  wire \result_o[30]_INST_0_i_13_n_0 ;
  wire \result_o[30]_INST_0_i_14_n_0 ;
  wire \result_o[30]_INST_0_i_15_n_0 ;
  wire \result_o[30]_INST_0_i_16_n_0 ;
  wire \result_o[30]_INST_0_i_17_n_0 ;
  wire \result_o[30]_INST_0_i_1_n_0 ;
  wire \result_o[30]_INST_0_i_2_n_0 ;
  wire \result_o[30]_INST_0_i_3_n_0 ;
  wire \result_o[30]_INST_0_i_4_n_0 ;
  wire \result_o[30]_INST_0_i_5_n_0 ;
  wire \result_o[30]_INST_0_i_6_n_0 ;
  wire \result_o[30]_INST_0_i_7_n_0 ;
  wire \result_o[30]_INST_0_i_8_n_0 ;
  wire \result_o[30]_INST_0_i_9_n_0 ;
  wire \result_o[31]_INST_0_i_10_n_0 ;
  wire \result_o[31]_INST_0_i_11_n_0 ;
  wire \result_o[31]_INST_0_i_12_n_0 ;
  wire \result_o[31]_INST_0_i_13_n_0 ;
  wire \result_o[31]_INST_0_i_14_n_0 ;
  wire \result_o[31]_INST_0_i_15_n_0 ;
  wire \result_o[31]_INST_0_i_16_n_0 ;
  wire \result_o[31]_INST_0_i_17_n_0 ;
  wire \result_o[31]_INST_0_i_18_n_1 ;
  wire \result_o[31]_INST_0_i_18_n_2 ;
  wire \result_o[31]_INST_0_i_18_n_3 ;
  wire \result_o[31]_INST_0_i_19_n_0 ;
  wire \result_o[31]_INST_0_i_1_n_0 ;
  wire \result_o[31]_INST_0_i_20_n_0 ;
  wire \result_o[31]_INST_0_i_21_n_0 ;
  wire \result_o[31]_INST_0_i_22_n_0 ;
  wire \result_o[31]_INST_0_i_23_n_0 ;
  wire \result_o[31]_INST_0_i_24_n_0 ;
  wire \result_o[31]_INST_0_i_25_n_0 ;
  wire \result_o[31]_INST_0_i_26_n_0 ;
  wire \result_o[31]_INST_0_i_27_n_0 ;
  wire \result_o[31]_INST_0_i_28_n_0 ;
  wire \result_o[31]_INST_0_i_29_n_0 ;
  wire \result_o[31]_INST_0_i_2_n_0 ;
  wire \result_o[31]_INST_0_i_30_n_0 ;
  wire \result_o[31]_INST_0_i_31_n_0 ;
  wire \result_o[31]_INST_0_i_32_n_0 ;
  wire \result_o[31]_INST_0_i_3_n_0 ;
  wire \result_o[31]_INST_0_i_4_n_0 ;
  wire \result_o[31]_INST_0_i_5_n_0 ;
  wire \result_o[31]_INST_0_i_6_n_0 ;
  wire \result_o[31]_INST_0_i_7_n_0 ;
  wire \result_o[31]_INST_0_i_8_n_0 ;
  wire \result_o[31]_INST_0_i_9_n_0 ;
  wire \result_o[3]_INST_0_i_10_n_0 ;
  wire \result_o[3]_INST_0_i_10_n_1 ;
  wire \result_o[3]_INST_0_i_10_n_2 ;
  wire \result_o[3]_INST_0_i_10_n_3 ;
  wire \result_o[3]_INST_0_i_11_n_0 ;
  wire \result_o[3]_INST_0_i_12_n_0 ;
  wire \result_o[3]_INST_0_i_12_n_1 ;
  wire \result_o[3]_INST_0_i_12_n_2 ;
  wire \result_o[3]_INST_0_i_12_n_3 ;
  wire \result_o[3]_INST_0_i_13_n_0 ;
  wire \result_o[3]_INST_0_i_14_n_0 ;
  wire \result_o[3]_INST_0_i_15_n_0 ;
  wire \result_o[3]_INST_0_i_16_n_0 ;
  wire \result_o[3]_INST_0_i_17_n_0 ;
  wire \result_o[3]_INST_0_i_18_n_0 ;
  wire \result_o[3]_INST_0_i_19_n_0 ;
  wire \result_o[3]_INST_0_i_1_n_0 ;
  wire \result_o[3]_INST_0_i_20_n_0 ;
  wire \result_o[3]_INST_0_i_21_n_0 ;
  wire \result_o[3]_INST_0_i_22_n_0 ;
  wire \result_o[3]_INST_0_i_23_n_0 ;
  wire \result_o[3]_INST_0_i_2_n_0 ;
  wire \result_o[3]_INST_0_i_3_n_0 ;
  wire \result_o[3]_INST_0_i_4_n_0 ;
  wire \result_o[3]_INST_0_i_5_n_0 ;
  wire \result_o[3]_INST_0_i_6_n_0 ;
  wire \result_o[3]_INST_0_i_7_n_0 ;
  wire \result_o[3]_INST_0_i_8_n_0 ;
  wire \result_o[3]_INST_0_i_9_n_0 ;
  wire \result_o[4]_INST_0_i_10_n_0 ;
  wire \result_o[4]_INST_0_i_1_n_0 ;
  wire \result_o[4]_INST_0_i_2_n_0 ;
  wire \result_o[4]_INST_0_i_3_n_0 ;
  wire \result_o[4]_INST_0_i_4_n_0 ;
  wire \result_o[4]_INST_0_i_5_n_0 ;
  wire \result_o[4]_INST_0_i_6_n_0 ;
  wire \result_o[4]_INST_0_i_7_n_0 ;
  wire \result_o[4]_INST_0_i_8_n_0 ;
  wire \result_o[4]_INST_0_i_9_n_0 ;
  wire \result_o[5]_INST_0_i_10_n_0 ;
  wire \result_o[5]_INST_0_i_1_n_0 ;
  wire \result_o[5]_INST_0_i_2_n_0 ;
  wire \result_o[5]_INST_0_i_3_n_0 ;
  wire \result_o[5]_INST_0_i_4_n_0 ;
  wire \result_o[5]_INST_0_i_5_n_0 ;
  wire \result_o[5]_INST_0_i_6_n_0 ;
  wire \result_o[5]_INST_0_i_7_n_0 ;
  wire \result_o[5]_INST_0_i_8_n_0 ;
  wire \result_o[5]_INST_0_i_9_n_0 ;
  wire \result_o[6]_INST_0_i_10_n_0 ;
  wire \result_o[6]_INST_0_i_1_n_0 ;
  wire \result_o[6]_INST_0_i_2_n_0 ;
  wire \result_o[6]_INST_0_i_3_n_0 ;
  wire \result_o[6]_INST_0_i_4_n_0 ;
  wire \result_o[6]_INST_0_i_5_n_0 ;
  wire \result_o[6]_INST_0_i_6_n_0 ;
  wire \result_o[6]_INST_0_i_7_n_0 ;
  wire \result_o[6]_INST_0_i_8_n_0 ;
  wire \result_o[6]_INST_0_i_9_n_0 ;
  wire \result_o[7]_INST_0_i_10_n_0 ;
  wire \result_o[7]_INST_0_i_11_n_0 ;
  wire \result_o[7]_INST_0_i_11_n_1 ;
  wire \result_o[7]_INST_0_i_11_n_2 ;
  wire \result_o[7]_INST_0_i_11_n_3 ;
  wire \result_o[7]_INST_0_i_12_n_0 ;
  wire \result_o[7]_INST_0_i_13_n_0 ;
  wire \result_o[7]_INST_0_i_14_n_0 ;
  wire \result_o[7]_INST_0_i_15_n_0 ;
  wire \result_o[7]_INST_0_i_16_n_0 ;
  wire \result_o[7]_INST_0_i_17_n_0 ;
  wire \result_o[7]_INST_0_i_18_n_0 ;
  wire \result_o[7]_INST_0_i_19_n_0 ;
  wire \result_o[7]_INST_0_i_1_n_0 ;
  wire \result_o[7]_INST_0_i_20_n_0 ;
  wire \result_o[7]_INST_0_i_21_n_0 ;
  wire \result_o[7]_INST_0_i_2_n_0 ;
  wire \result_o[7]_INST_0_i_3_n_0 ;
  wire \result_o[7]_INST_0_i_4_n_0 ;
  wire \result_o[7]_INST_0_i_5_n_0 ;
  wire \result_o[7]_INST_0_i_6_n_0 ;
  wire \result_o[7]_INST_0_i_7_n_0 ;
  wire \result_o[7]_INST_0_i_8_n_0 ;
  wire \result_o[7]_INST_0_i_9_n_0 ;
  wire \result_o[7]_INST_0_i_9_n_1 ;
  wire \result_o[7]_INST_0_i_9_n_2 ;
  wire \result_o[7]_INST_0_i_9_n_3 ;
  wire \result_o[8]_INST_0_i_10_n_0 ;
  wire \result_o[8]_INST_0_i_11_n_0 ;
  wire \result_o[8]_INST_0_i_12_n_0 ;
  wire \result_o[8]_INST_0_i_1_n_0 ;
  wire \result_o[8]_INST_0_i_2_n_0 ;
  wire \result_o[8]_INST_0_i_3_n_0 ;
  wire \result_o[8]_INST_0_i_4_n_0 ;
  wire \result_o[8]_INST_0_i_5_n_0 ;
  wire \result_o[8]_INST_0_i_6_n_0 ;
  wire \result_o[8]_INST_0_i_7_n_0 ;
  wire \result_o[8]_INST_0_i_8_n_0 ;
  wire \result_o[8]_INST_0_i_9_n_0 ;
  wire \result_o[9]_INST_0_i_10_n_0 ;
  wire \result_o[9]_INST_0_i_1_n_0 ;
  wire \result_o[9]_INST_0_i_2_n_0 ;
  wire \result_o[9]_INST_0_i_3_n_0 ;
  wire \result_o[9]_INST_0_i_4_n_0 ;
  wire \result_o[9]_INST_0_i_5_n_0 ;
  wire \result_o[9]_INST_0_i_6_n_0 ;
  wire \result_o[9]_INST_0_i_7_n_0 ;
  wire \result_o[9]_INST_0_i_8_n_0 ;
  wire \result_o[9]_INST_0_i_9_n_0 ;

  GND GND
       (.G(\<const0> ));
  VCC VCC
       (.P(\<const1> ));
  LUT4 #(
    .INIT(16'h8880)) 
    flag_o_INST_0
       (.I0(alu_op_i[4]),
        .I1(alu_op_i[3]),
        .I2(flag_o_INST_0_i_1_n_0),
        .I3(flag_o_INST_0_i_2_n_0),
        .O(flag_o));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT5 #(
    .INIT(32'h000000E2)) 
    flag_o_INST_0_i_1
       (.I0(flag_o_INST_0_i_3_n_1),
        .I1(alu_op_i[0]),
        .I2(flag_o_INST_0_i_4_n_1),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .O(flag_o_INST_0_i_1_n_0));
  CARRY4 flag_o_INST_0_i_10
       (.CI(flag_o_INST_0_i_28_n_0),
        .CO({flag_o_INST_0_i_10_n_0,flag_o_INST_0_i_10_n_1,flag_o_INST_0_i_10_n_2,flag_o_INST_0_i_10_n_3}),
        .CYINIT(\<const0> ),
        .DI({\<const1> ,\<const1> ,\<const1> ,\<const1> }),
        .S({flag_o_INST_0_i_29_n_0,flag_o_INST_0_i_30_n_0,flag_o_INST_0_i_31_n_0,flag_o_INST_0_i_32_n_0}));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_11
       (.I0(b_i[30]),
        .I1(a_i[30]),
        .I2(b_i[31]),
        .I3(a_i[31]),
        .O(flag_o_INST_0_i_11_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_12
       (.I0(a_i[29]),
        .I1(b_i[29]),
        .I2(a_i[28]),
        .I3(b_i[28]),
        .I4(b_i[27]),
        .I5(a_i[27]),
        .O(flag_o_INST_0_i_12_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_13
       (.I0(a_i[26]),
        .I1(b_i[26]),
        .I2(a_i[25]),
        .I3(b_i[25]),
        .I4(b_i[24]),
        .I5(a_i[24]),
        .O(flag_o_INST_0_i_13_n_0));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 flag_o_INST_0_i_14
       (.CI(flag_o_INST_0_i_33_n_0),
        .CO({flag_o_INST_0_i_14_n_0,flag_o_INST_0_i_14_n_1,flag_o_INST_0_i_14_n_2,flag_o_INST_0_i_14_n_3}),
        .CYINIT(\<const0> ),
        .DI({flag_o_INST_0_i_34_n_0,flag_o_INST_0_i_35_n_0,flag_o_INST_0_i_36_n_0,flag_o_INST_0_i_37_n_0}),
        .S({flag_o_INST_0_i_38_n_0,flag_o_INST_0_i_39_n_0,flag_o_INST_0_i_40_n_0,flag_o_INST_0_i_41_n_0}));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_15
       (.I0(a_i[30]),
        .I1(b_i[30]),
        .I2(a_i[31]),
        .I3(b_i[31]),
        .O(flag_o_INST_0_i_15_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_16
       (.I0(a_i[28]),
        .I1(b_i[28]),
        .I2(b_i[29]),
        .I3(a_i[29]),
        .O(flag_o_INST_0_i_16_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_17
       (.I0(a_i[26]),
        .I1(b_i[26]),
        .I2(b_i[27]),
        .I3(a_i[27]),
        .O(flag_o_INST_0_i_17_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_18
       (.I0(a_i[24]),
        .I1(b_i[24]),
        .I2(b_i[25]),
        .I3(a_i[25]),
        .O(flag_o_INST_0_i_18_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_19
       (.I0(b_i[31]),
        .I1(a_i[31]),
        .I2(b_i[30]),
        .I3(a_i[30]),
        .O(flag_o_INST_0_i_19_n_0));
  LUT6 #(
    .INIT(64'h2828AAA028280A00)) 
    flag_o_INST_0_i_2
       (.I0(alu_op_i[2]),
        .I1(data4),
        .I2(alu_op_i[0]),
        .I3(\result_o[0]_INST_0_i_13_n_0 ),
        .I4(alu_op_i[1]),
        .I5(data3),
        .O(flag_o_INST_0_i_2_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_20
       (.I0(b_i[29]),
        .I1(a_i[29]),
        .I2(b_i[28]),
        .I3(a_i[28]),
        .O(flag_o_INST_0_i_20_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_21
       (.I0(b_i[27]),
        .I1(a_i[27]),
        .I2(b_i[26]),
        .I3(a_i[26]),
        .O(flag_o_INST_0_i_21_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_22
       (.I0(b_i[25]),
        .I1(a_i[25]),
        .I2(b_i[24]),
        .I3(a_i[24]),
        .O(flag_o_INST_0_i_22_n_0));
  CARRY4 flag_o_INST_0_i_23
       (.CI(\<const0> ),
        .CO({flag_o_INST_0_i_23_n_0,flag_o_INST_0_i_23_n_1,flag_o_INST_0_i_23_n_2,flag_o_INST_0_i_23_n_3}),
        .CYINIT(\<const1> ),
        .DI({\<const0> ,\<const0> ,\<const0> ,\<const0> }),
        .S({flag_o_INST_0_i_42_n_0,flag_o_INST_0_i_43_n_0,flag_o_INST_0_i_44_n_0,flag_o_INST_0_i_45_n_0}));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_24
       (.I0(a_i[23]),
        .I1(b_i[23]),
        .I2(a_i[22]),
        .I3(b_i[22]),
        .I4(b_i[21]),
        .I5(a_i[21]),
        .O(flag_o_INST_0_i_24_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_25
       (.I0(a_i[20]),
        .I1(b_i[20]),
        .I2(a_i[19]),
        .I3(b_i[19]),
        .I4(b_i[18]),
        .I5(a_i[18]),
        .O(flag_o_INST_0_i_25_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_26
       (.I0(a_i[17]),
        .I1(b_i[17]),
        .I2(a_i[16]),
        .I3(b_i[16]),
        .I4(b_i[15]),
        .I5(a_i[15]),
        .O(flag_o_INST_0_i_26_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_27
       (.I0(a_i[14]),
        .I1(b_i[14]),
        .I2(a_i[13]),
        .I3(b_i[13]),
        .I4(b_i[12]),
        .I5(a_i[12]),
        .O(flag_o_INST_0_i_27_n_0));
  CARRY4 flag_o_INST_0_i_28
       (.CI(\<const0> ),
        .CO({flag_o_INST_0_i_28_n_0,flag_o_INST_0_i_28_n_1,flag_o_INST_0_i_28_n_2,flag_o_INST_0_i_28_n_3}),
        .CYINIT(\<const0> ),
        .DI({\<const1> ,\<const1> ,\<const1> ,\<const1> }),
        .S({flag_o_INST_0_i_46_n_0,flag_o_INST_0_i_47_n_0,flag_o_INST_0_i_48_n_0,flag_o_INST_0_i_49_n_0}));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_29
       (.I0(a_i[23]),
        .I1(b_i[23]),
        .I2(a_i[22]),
        .I3(b_i[22]),
        .I4(b_i[21]),
        .I5(a_i[21]),
        .O(flag_o_INST_0_i_29_n_0));
  CARRY4 flag_o_INST_0_i_3
       (.CI(flag_o_INST_0_i_6_n_0),
        .CO({flag_o_INST_0_i_3_n_1,flag_o_INST_0_i_3_n_2,flag_o_INST_0_i_3_n_3}),
        .CYINIT(\<const0> ),
        .DI({\<const0> ,\<const0> ,\<const0> ,\<const0> }),
        .S({\<const0> ,flag_o_INST_0_i_7_n_0,flag_o_INST_0_i_8_n_0,flag_o_INST_0_i_9_n_0}));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_30
       (.I0(a_i[20]),
        .I1(b_i[20]),
        .I2(a_i[19]),
        .I3(b_i[19]),
        .I4(b_i[18]),
        .I5(a_i[18]),
        .O(flag_o_INST_0_i_30_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_31
       (.I0(a_i[17]),
        .I1(b_i[17]),
        .I2(a_i[16]),
        .I3(b_i[16]),
        .I4(b_i[15]),
        .I5(a_i[15]),
        .O(flag_o_INST_0_i_31_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_32
       (.I0(a_i[14]),
        .I1(b_i[14]),
        .I2(a_i[13]),
        .I3(b_i[13]),
        .I4(b_i[12]),
        .I5(a_i[12]),
        .O(flag_o_INST_0_i_32_n_0));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 flag_o_INST_0_i_33
       (.CI(flag_o_INST_0_i_50_n_0),
        .CO({flag_o_INST_0_i_33_n_0,flag_o_INST_0_i_33_n_1,flag_o_INST_0_i_33_n_2,flag_o_INST_0_i_33_n_3}),
        .CYINIT(\<const0> ),
        .DI({flag_o_INST_0_i_51_n_0,flag_o_INST_0_i_52_n_0,flag_o_INST_0_i_53_n_0,flag_o_INST_0_i_54_n_0}),
        .S({flag_o_INST_0_i_55_n_0,flag_o_INST_0_i_56_n_0,flag_o_INST_0_i_57_n_0,flag_o_INST_0_i_58_n_0}));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_34
       (.I0(a_i[22]),
        .I1(b_i[22]),
        .I2(b_i[23]),
        .I3(a_i[23]),
        .O(flag_o_INST_0_i_34_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_35
       (.I0(a_i[20]),
        .I1(b_i[20]),
        .I2(b_i[21]),
        .I3(a_i[21]),
        .O(flag_o_INST_0_i_35_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_36
       (.I0(a_i[18]),
        .I1(b_i[18]),
        .I2(b_i[19]),
        .I3(a_i[19]),
        .O(flag_o_INST_0_i_36_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_37
       (.I0(a_i[16]),
        .I1(b_i[16]),
        .I2(b_i[17]),
        .I3(a_i[17]),
        .O(flag_o_INST_0_i_37_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_38
       (.I0(b_i[23]),
        .I1(a_i[23]),
        .I2(b_i[22]),
        .I3(a_i[22]),
        .O(flag_o_INST_0_i_38_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_39
       (.I0(b_i[21]),
        .I1(a_i[21]),
        .I2(b_i[20]),
        .I3(a_i[20]),
        .O(flag_o_INST_0_i_39_n_0));
  CARRY4 flag_o_INST_0_i_4
       (.CI(flag_o_INST_0_i_10_n_0),
        .CO({flag_o_INST_0_i_4_n_1,flag_o_INST_0_i_4_n_2,flag_o_INST_0_i_4_n_3}),
        .CYINIT(\<const0> ),
        .DI({\<const0> ,\<const1> ,\<const1> ,\<const1> }),
        .S({\<const0> ,flag_o_INST_0_i_11_n_0,flag_o_INST_0_i_12_n_0,flag_o_INST_0_i_13_n_0}));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_40
       (.I0(b_i[19]),
        .I1(a_i[19]),
        .I2(b_i[18]),
        .I3(a_i[18]),
        .O(flag_o_INST_0_i_40_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_41
       (.I0(b_i[17]),
        .I1(a_i[17]),
        .I2(b_i[16]),
        .I3(a_i[16]),
        .O(flag_o_INST_0_i_41_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_42
       (.I0(a_i[11]),
        .I1(b_i[11]),
        .I2(a_i[10]),
        .I3(b_i[10]),
        .I4(b_i[9]),
        .I5(a_i[9]),
        .O(flag_o_INST_0_i_42_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_43
       (.I0(a_i[8]),
        .I1(b_i[8]),
        .I2(a_i[7]),
        .I3(b_i[7]),
        .I4(b_i[6]),
        .I5(a_i[6]),
        .O(flag_o_INST_0_i_43_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_44
       (.I0(a_i[5]),
        .I1(b_i[5]),
        .I2(a_i[4]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[3]),
        .O(flag_o_INST_0_i_44_n_0));
  LUT6 #(
    .INIT(64'h9000090000900009)) 
    flag_o_INST_0_i_45
       (.I0(a_i[0]),
        .I1(b_i[0]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[1]),
        .I5(a_i[2]),
        .O(flag_o_INST_0_i_45_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_46
       (.I0(a_i[11]),
        .I1(b_i[11]),
        .I2(a_i[10]),
        .I3(b_i[10]),
        .I4(b_i[9]),
        .I5(a_i[9]),
        .O(flag_o_INST_0_i_46_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_47
       (.I0(a_i[8]),
        .I1(b_i[8]),
        .I2(a_i[7]),
        .I3(b_i[7]),
        .I4(b_i[6]),
        .I5(a_i[6]),
        .O(flag_o_INST_0_i_47_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_48
       (.I0(a_i[5]),
        .I1(b_i[5]),
        .I2(a_i[4]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[3]),
        .O(flag_o_INST_0_i_48_n_0));
  LUT6 #(
    .INIT(64'h9000090000900009)) 
    flag_o_INST_0_i_49
       (.I0(a_i[0]),
        .I1(b_i[0]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[1]),
        .I5(a_i[2]),
        .O(flag_o_INST_0_i_49_n_0));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 flag_o_INST_0_i_5
       (.CI(flag_o_INST_0_i_14_n_0),
        .CO({data3,flag_o_INST_0_i_5_n_1,flag_o_INST_0_i_5_n_2,flag_o_INST_0_i_5_n_3}),
        .CYINIT(\<const0> ),
        .DI({flag_o_INST_0_i_15_n_0,flag_o_INST_0_i_16_n_0,flag_o_INST_0_i_17_n_0,flag_o_INST_0_i_18_n_0}),
        .S({flag_o_INST_0_i_19_n_0,flag_o_INST_0_i_20_n_0,flag_o_INST_0_i_21_n_0,flag_o_INST_0_i_22_n_0}));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 flag_o_INST_0_i_50
       (.CI(\<const0> ),
        .CO({flag_o_INST_0_i_50_n_0,flag_o_INST_0_i_50_n_1,flag_o_INST_0_i_50_n_2,flag_o_INST_0_i_50_n_3}),
        .CYINIT(\<const1> ),
        .DI({flag_o_INST_0_i_59_n_0,flag_o_INST_0_i_60_n_0,flag_o_INST_0_i_61_n_0,flag_o_INST_0_i_62_n_0}),
        .S({flag_o_INST_0_i_63_n_0,flag_o_INST_0_i_64_n_0,flag_o_INST_0_i_65_n_0,flag_o_INST_0_i_66_n_0}));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_51
       (.I0(a_i[14]),
        .I1(b_i[14]),
        .I2(b_i[15]),
        .I3(a_i[15]),
        .O(flag_o_INST_0_i_51_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_52
       (.I0(a_i[12]),
        .I1(b_i[12]),
        .I2(b_i[13]),
        .I3(a_i[13]),
        .O(flag_o_INST_0_i_52_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_53
       (.I0(a_i[10]),
        .I1(b_i[10]),
        .I2(b_i[11]),
        .I3(a_i[11]),
        .O(flag_o_INST_0_i_53_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_54
       (.I0(a_i[8]),
        .I1(b_i[8]),
        .I2(b_i[9]),
        .I3(a_i[9]),
        .O(flag_o_INST_0_i_54_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_55
       (.I0(b_i[15]),
        .I1(a_i[15]),
        .I2(b_i[14]),
        .I3(a_i[14]),
        .O(flag_o_INST_0_i_55_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_56
       (.I0(b_i[13]),
        .I1(a_i[13]),
        .I2(b_i[12]),
        .I3(a_i[12]),
        .O(flag_o_INST_0_i_56_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_57
       (.I0(b_i[11]),
        .I1(a_i[11]),
        .I2(b_i[10]),
        .I3(a_i[10]),
        .O(flag_o_INST_0_i_57_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_58
       (.I0(b_i[9]),
        .I1(a_i[9]),
        .I2(b_i[8]),
        .I3(a_i[8]),
        .O(flag_o_INST_0_i_58_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_59
       (.I0(a_i[6]),
        .I1(b_i[6]),
        .I2(b_i[7]),
        .I3(a_i[7]),
        .O(flag_o_INST_0_i_59_n_0));
  CARRY4 flag_o_INST_0_i_6
       (.CI(flag_o_INST_0_i_23_n_0),
        .CO({flag_o_INST_0_i_6_n_0,flag_o_INST_0_i_6_n_1,flag_o_INST_0_i_6_n_2,flag_o_INST_0_i_6_n_3}),
        .CYINIT(\<const0> ),
        .DI({\<const0> ,\<const0> ,\<const0> ,\<const0> }),
        .S({flag_o_INST_0_i_24_n_0,flag_o_INST_0_i_25_n_0,flag_o_INST_0_i_26_n_0,flag_o_INST_0_i_27_n_0}));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_60
       (.I0(a_i[4]),
        .I1(b_i[4]),
        .I2(b_i[5]),
        .I3(a_i[5]),
        .O(flag_o_INST_0_i_60_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_61
       (.I0(a_i[2]),
        .I1(b_i[2]),
        .I2(b_i[3]),
        .I3(a_i[3]),
        .O(flag_o_INST_0_i_61_n_0));
  LUT4 #(
    .INIT(16'h2F02)) 
    flag_o_INST_0_i_62
       (.I0(a_i[0]),
        .I1(b_i[0]),
        .I2(b_i[1]),
        .I3(a_i[1]),
        .O(flag_o_INST_0_i_62_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_63
       (.I0(b_i[7]),
        .I1(a_i[7]),
        .I2(b_i[6]),
        .I3(a_i[6]),
        .O(flag_o_INST_0_i_63_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_64
       (.I0(b_i[5]),
        .I1(a_i[5]),
        .I2(b_i[4]),
        .I3(a_i[4]),
        .O(flag_o_INST_0_i_64_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_65
       (.I0(b_i[3]),
        .I1(a_i[3]),
        .I2(b_i[2]),
        .I3(a_i[2]),
        .O(flag_o_INST_0_i_65_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_66
       (.I0(b_i[1]),
        .I1(a_i[1]),
        .I2(b_i[0]),
        .I3(a_i[0]),
        .O(flag_o_INST_0_i_66_n_0));
  LUT4 #(
    .INIT(16'h9009)) 
    flag_o_INST_0_i_7
       (.I0(b_i[30]),
        .I1(a_i[30]),
        .I2(b_i[31]),
        .I3(a_i[31]),
        .O(flag_o_INST_0_i_7_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_8
       (.I0(a_i[29]),
        .I1(b_i[29]),
        .I2(a_i[28]),
        .I3(b_i[28]),
        .I4(b_i[27]),
        .I5(a_i[27]),
        .O(flag_o_INST_0_i_8_n_0));
  LUT6 #(
    .INIT(64'h9009000000009009)) 
    flag_o_INST_0_i_9
       (.I0(a_i[26]),
        .I1(b_i[26]),
        .I2(a_i[25]),
        .I3(b_i[25]),
        .I4(b_i[24]),
        .I5(a_i[24]),
        .O(flag_o_INST_0_i_9_n_0));
  LUT6 #(
    .INIT(64'hFFFFFEEEFEEEFEEE)) 
    \result_o[0]_INST_0 
       (.I0(\result_o[0]_INST_0_i_1_n_0 ),
        .I1(\result_o[0]_INST_0_i_2_n_0 ),
        .I2(\result_o[0]_INST_0_i_3_n_0 ),
        .I3(data6),
        .I4(\result_o[0]_INST_0_i_5_n_0 ),
        .I5(\result_o[0]_INST_0_i_6_n_0 ),
        .O(result_o[0]));
  LUT6 #(
    .INIT(64'h0023000000200000)) 
    \result_o[0]_INST_0_i_1 
       (.I0(\result_o[0]_INST_0_i_7_n_0 ),
        .I1(alu_op_i[1]),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(\result_o[30]_INST_0_i_2_n_0 ),
        .I5(data0[0]),
        .O(\result_o[0]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h4444444044404440)) 
    \result_o[0]_INST_0_i_10 
       (.I0(b_i[0]),
        .I1(b_i[1]),
        .I2(\result_o[2]_INST_0_i_14_n_0 ),
        .I3(\result_o[2]_INST_0_i_13_n_0 ),
        .I4(b_i[2]),
        .I5(\result_o[6]_INST_0_i_10_n_0 ),
        .O(\result_o[0]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000B00080)) 
    \result_o[0]_INST_0_i_11 
       (.I0(a_i[24]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(\result_o[30]_INST_0_i_8_n_0 ),
        .I4(a_i[16]),
        .I5(b_i[0]),
        .O(\result_o[0]_INST_0_i_11_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_12 
       (.CI(\result_o[0]_INST_0_i_15_n_0 ),
        .CO({data4,\result_o[0]_INST_0_i_12_n_1 ,\result_o[0]_INST_0_i_12_n_2 ,\result_o[0]_INST_0_i_12_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_16_n_0 ,\result_o[0]_INST_0_i_17_n_0 ,\result_o[0]_INST_0_i_18_n_0 ,\result_o[0]_INST_0_i_19_n_0 }),
        .S({\result_o[0]_INST_0_i_20_n_0 ,\result_o[0]_INST_0_i_21_n_0 ,\result_o[0]_INST_0_i_22_n_0 ,\result_o[0]_INST_0_i_23_n_0 }));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_13 
       (.CI(\result_o[0]_INST_0_i_24_n_0 ),
        .CO({\result_o[0]_INST_0_i_13_n_0 ,\result_o[0]_INST_0_i_13_n_1 ,\result_o[0]_INST_0_i_13_n_2 ,\result_o[0]_INST_0_i_13_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_25_n_0 ,\result_o[0]_INST_0_i_26_n_0 ,\result_o[0]_INST_0_i_27_n_0 ,\result_o[0]_INST_0_i_28_n_0 }),
        .S({\result_o[0]_INST_0_i_29_n_0 ,\result_o[0]_INST_0_i_30_n_0 ,\result_o[0]_INST_0_i_31_n_0 ,\result_o[0]_INST_0_i_32_n_0 }));
  LUT6 #(
    .INIT(64'h0000000000040000)) 
    \result_o[0]_INST_0_i_14 
       (.I0(b_i[0]),
        .I1(a_i[8]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[0]_INST_0_i_14_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_15 
       (.CI(\result_o[0]_INST_0_i_33_n_0 ),
        .CO({\result_o[0]_INST_0_i_15_n_0 ,\result_o[0]_INST_0_i_15_n_1 ,\result_o[0]_INST_0_i_15_n_2 ,\result_o[0]_INST_0_i_15_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_34_n_0 ,\result_o[0]_INST_0_i_35_n_0 ,\result_o[0]_INST_0_i_36_n_0 ,\result_o[0]_INST_0_i_37_n_0 }),
        .S({\result_o[0]_INST_0_i_38_n_0 ,\result_o[0]_INST_0_i_39_n_0 ,\result_o[0]_INST_0_i_40_n_0 ,\result_o[0]_INST_0_i_41_n_0 }));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_16 
       (.I0(b_i[30]),
        .I1(a_i[30]),
        .I2(a_i[31]),
        .I3(b_i[31]),
        .O(\result_o[0]_INST_0_i_16_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_17 
       (.I0(b_i[28]),
        .I1(a_i[28]),
        .I2(a_i[29]),
        .I3(b_i[29]),
        .O(\result_o[0]_INST_0_i_17_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_18 
       (.I0(b_i[26]),
        .I1(a_i[26]),
        .I2(a_i[27]),
        .I3(b_i[27]),
        .O(\result_o[0]_INST_0_i_18_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_19 
       (.I0(b_i[24]),
        .I1(a_i[24]),
        .I2(a_i[25]),
        .I3(b_i[25]),
        .O(\result_o[0]_INST_0_i_19_n_0 ));
  LUT6 #(
    .INIT(64'hF888888888888888)) 
    \result_o[0]_INST_0_i_2 
       (.I0(data1[0]),
        .I1(\result_o[28]_INST_0_i_4_n_0 ),
        .I2(\result_o[31]_INST_0_i_11_n_0 ),
        .I3(a_i[0]),
        .I4(\result_o[30]_INST_0_i_2_n_0 ),
        .I5(\result_o[0]_INST_0_i_8_n_0 ),
        .O(\result_o[0]_INST_0_i_2_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_20 
       (.I0(b_i[31]),
        .I1(a_i[31]),
        .I2(b_i[30]),
        .I3(a_i[30]),
        .O(\result_o[0]_INST_0_i_20_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_21 
       (.I0(b_i[29]),
        .I1(a_i[29]),
        .I2(b_i[28]),
        .I3(a_i[28]),
        .O(\result_o[0]_INST_0_i_21_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_22 
       (.I0(b_i[27]),
        .I1(a_i[27]),
        .I2(b_i[26]),
        .I3(a_i[26]),
        .O(\result_o[0]_INST_0_i_22_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_23 
       (.I0(b_i[25]),
        .I1(a_i[25]),
        .I2(b_i[24]),
        .I3(a_i[24]),
        .O(\result_o[0]_INST_0_i_23_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_24 
       (.CI(\result_o[0]_INST_0_i_42_n_0 ),
        .CO({\result_o[0]_INST_0_i_24_n_0 ,\result_o[0]_INST_0_i_24_n_1 ,\result_o[0]_INST_0_i_24_n_2 ,\result_o[0]_INST_0_i_24_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_43_n_0 ,\result_o[0]_INST_0_i_44_n_0 ,\result_o[0]_INST_0_i_45_n_0 ,\result_o[0]_INST_0_i_46_n_0 }),
        .S({\result_o[0]_INST_0_i_47_n_0 ,\result_o[0]_INST_0_i_48_n_0 ,\result_o[0]_INST_0_i_49_n_0 ,\result_o[0]_INST_0_i_50_n_0 }));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_25 
       (.I0(b_i[30]),
        .I1(a_i[30]),
        .I2(b_i[31]),
        .I3(a_i[31]),
        .O(\result_o[0]_INST_0_i_25_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_26 
       (.I0(b_i[28]),
        .I1(a_i[28]),
        .I2(a_i[29]),
        .I3(b_i[29]),
        .O(\result_o[0]_INST_0_i_26_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_27 
       (.I0(b_i[26]),
        .I1(a_i[26]),
        .I2(a_i[27]),
        .I3(b_i[27]),
        .O(\result_o[0]_INST_0_i_27_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_28 
       (.I0(b_i[24]),
        .I1(a_i[24]),
        .I2(a_i[25]),
        .I3(b_i[25]),
        .O(\result_o[0]_INST_0_i_28_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_29 
       (.I0(b_i[31]),
        .I1(a_i[31]),
        .I2(b_i[30]),
        .I3(a_i[30]),
        .O(\result_o[0]_INST_0_i_29_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT4 #(
    .INIT(16'h0008)) 
    \result_o[0]_INST_0_i_3 
       (.I0(alu_op_i[2]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[4]),
        .O(\result_o[0]_INST_0_i_3_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_30 
       (.I0(b_i[29]),
        .I1(a_i[29]),
        .I2(b_i[28]),
        .I3(a_i[28]),
        .O(\result_o[0]_INST_0_i_30_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_31 
       (.I0(b_i[27]),
        .I1(a_i[27]),
        .I2(b_i[26]),
        .I3(a_i[26]),
        .O(\result_o[0]_INST_0_i_31_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_32 
       (.I0(b_i[25]),
        .I1(a_i[25]),
        .I2(b_i[24]),
        .I3(a_i[24]),
        .O(\result_o[0]_INST_0_i_32_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_33 
       (.CI(\result_o[0]_INST_0_i_51_n_0 ),
        .CO({\result_o[0]_INST_0_i_33_n_0 ,\result_o[0]_INST_0_i_33_n_1 ,\result_o[0]_INST_0_i_33_n_2 ,\result_o[0]_INST_0_i_33_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_52_n_0 ,\result_o[0]_INST_0_i_53_n_0 ,\result_o[0]_INST_0_i_54_n_0 ,\result_o[0]_INST_0_i_55_n_0 }),
        .S({\result_o[0]_INST_0_i_56_n_0 ,\result_o[0]_INST_0_i_57_n_0 ,\result_o[0]_INST_0_i_58_n_0 ,\result_o[0]_INST_0_i_59_n_0 }));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_34 
       (.I0(b_i[22]),
        .I1(a_i[22]),
        .I2(a_i[23]),
        .I3(b_i[23]),
        .O(\result_o[0]_INST_0_i_34_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_35 
       (.I0(b_i[20]),
        .I1(a_i[20]),
        .I2(a_i[21]),
        .I3(b_i[21]),
        .O(\result_o[0]_INST_0_i_35_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_36 
       (.I0(b_i[18]),
        .I1(a_i[18]),
        .I2(a_i[19]),
        .I3(b_i[19]),
        .O(\result_o[0]_INST_0_i_36_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_37 
       (.I0(b_i[16]),
        .I1(a_i[16]),
        .I2(a_i[17]),
        .I3(b_i[17]),
        .O(\result_o[0]_INST_0_i_37_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_38 
       (.I0(b_i[23]),
        .I1(a_i[23]),
        .I2(b_i[22]),
        .I3(a_i[22]),
        .O(\result_o[0]_INST_0_i_38_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_39 
       (.I0(b_i[21]),
        .I1(a_i[21]),
        .I2(b_i[20]),
        .I3(a_i[20]),
        .O(\result_o[0]_INST_0_i_39_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFE0)) 
    \result_o[0]_INST_0_i_4 
       (.I0(\result_o[1]_INST_0_i_7_n_0 ),
        .I1(\result_o[1]_INST_0_i_6_n_0 ),
        .I2(b_i[0]),
        .I3(\result_o[0]_INST_0_i_9_n_0 ),
        .I4(\result_o[0]_INST_0_i_10_n_0 ),
        .I5(\result_o[0]_INST_0_i_11_n_0 ),
        .O(data6));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_40 
       (.I0(b_i[19]),
        .I1(a_i[19]),
        .I2(b_i[18]),
        .I3(a_i[18]),
        .O(\result_o[0]_INST_0_i_40_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_41 
       (.I0(b_i[17]),
        .I1(a_i[17]),
        .I2(b_i[16]),
        .I3(a_i[16]),
        .O(\result_o[0]_INST_0_i_41_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_42 
       (.CI(\result_o[0]_INST_0_i_60_n_0 ),
        .CO({\result_o[0]_INST_0_i_42_n_0 ,\result_o[0]_INST_0_i_42_n_1 ,\result_o[0]_INST_0_i_42_n_2 ,\result_o[0]_INST_0_i_42_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_61_n_0 ,\result_o[0]_INST_0_i_62_n_0 ,\result_o[0]_INST_0_i_63_n_0 ,\result_o[0]_INST_0_i_64_n_0 }),
        .S({\result_o[0]_INST_0_i_65_n_0 ,\result_o[0]_INST_0_i_66_n_0 ,\result_o[0]_INST_0_i_67_n_0 ,\result_o[0]_INST_0_i_68_n_0 }));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_43 
       (.I0(b_i[22]),
        .I1(a_i[22]),
        .I2(a_i[23]),
        .I3(b_i[23]),
        .O(\result_o[0]_INST_0_i_43_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_44 
       (.I0(b_i[20]),
        .I1(a_i[20]),
        .I2(a_i[21]),
        .I3(b_i[21]),
        .O(\result_o[0]_INST_0_i_44_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_45 
       (.I0(b_i[18]),
        .I1(a_i[18]),
        .I2(a_i[19]),
        .I3(b_i[19]),
        .O(\result_o[0]_INST_0_i_45_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_46 
       (.I0(b_i[16]),
        .I1(a_i[16]),
        .I2(a_i[17]),
        .I3(b_i[17]),
        .O(\result_o[0]_INST_0_i_46_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_47 
       (.I0(b_i[23]),
        .I1(a_i[23]),
        .I2(b_i[22]),
        .I3(a_i[22]),
        .O(\result_o[0]_INST_0_i_47_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_48 
       (.I0(b_i[21]),
        .I1(a_i[21]),
        .I2(b_i[20]),
        .I3(a_i[20]),
        .O(\result_o[0]_INST_0_i_48_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_49 
       (.I0(b_i[19]),
        .I1(a_i[19]),
        .I2(b_i[18]),
        .I3(a_i[18]),
        .O(\result_o[0]_INST_0_i_49_n_0 ));
  LUT3 #(
    .INIT(8'h10)) 
    \result_o[0]_INST_0_i_5 
       (.I0(alu_op_i[4]),
        .I1(alu_op_i[3]),
        .I2(alu_op_i[1]),
        .O(\result_o[0]_INST_0_i_5_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_50 
       (.I0(b_i[17]),
        .I1(a_i[17]),
        .I2(b_i[16]),
        .I3(a_i[16]),
        .O(\result_o[0]_INST_0_i_50_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_51 
       (.CI(\<const0> ),
        .CO({\result_o[0]_INST_0_i_51_n_0 ,\result_o[0]_INST_0_i_51_n_1 ,\result_o[0]_INST_0_i_51_n_2 ,\result_o[0]_INST_0_i_51_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_69_n_0 ,\result_o[0]_INST_0_i_70_n_0 ,\result_o[0]_INST_0_i_71_n_0 ,\result_o[0]_INST_0_i_72_n_0 }),
        .S({\result_o[0]_INST_0_i_73_n_0 ,\result_o[0]_INST_0_i_74_n_0 ,\result_o[0]_INST_0_i_75_n_0 ,\result_o[0]_INST_0_i_76_n_0 }));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_52 
       (.I0(b_i[14]),
        .I1(a_i[14]),
        .I2(a_i[15]),
        .I3(b_i[15]),
        .O(\result_o[0]_INST_0_i_52_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_53 
       (.I0(b_i[12]),
        .I1(a_i[12]),
        .I2(a_i[13]),
        .I3(b_i[13]),
        .O(\result_o[0]_INST_0_i_53_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_54 
       (.I0(b_i[10]),
        .I1(a_i[10]),
        .I2(a_i[11]),
        .I3(b_i[11]),
        .O(\result_o[0]_INST_0_i_54_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_55 
       (.I0(b_i[8]),
        .I1(a_i[8]),
        .I2(a_i[9]),
        .I3(b_i[9]),
        .O(\result_o[0]_INST_0_i_55_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_56 
       (.I0(b_i[15]),
        .I1(a_i[15]),
        .I2(b_i[14]),
        .I3(a_i[14]),
        .O(\result_o[0]_INST_0_i_56_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_57 
       (.I0(b_i[13]),
        .I1(a_i[13]),
        .I2(b_i[12]),
        .I3(a_i[12]),
        .O(\result_o[0]_INST_0_i_57_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_58 
       (.I0(b_i[11]),
        .I1(a_i[11]),
        .I2(b_i[10]),
        .I3(a_i[10]),
        .O(\result_o[0]_INST_0_i_58_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_59 
       (.I0(b_i[9]),
        .I1(a_i[9]),
        .I2(b_i[8]),
        .I3(a_i[8]),
        .O(\result_o[0]_INST_0_i_59_n_0 ));
  LUT6 #(
    .INIT(64'hF000AAAAFFF0CCCC)) 
    \result_o[0]_INST_0_i_6 
       (.I0(data4),
        .I1(\result_o[0]_INST_0_i_13_n_0 ),
        .I2(b_i[0]),
        .I3(a_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[0]_INST_0_i_6_n_0 ));
  (* COMPARATOR_THRESHOLD = "11" *) 
  CARRY4 \result_o[0]_INST_0_i_60 
       (.CI(\<const0> ),
        .CO({\result_o[0]_INST_0_i_60_n_0 ,\result_o[0]_INST_0_i_60_n_1 ,\result_o[0]_INST_0_i_60_n_2 ,\result_o[0]_INST_0_i_60_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\result_o[0]_INST_0_i_77_n_0 ,\result_o[0]_INST_0_i_78_n_0 ,\result_o[0]_INST_0_i_79_n_0 ,\result_o[0]_INST_0_i_80_n_0 }),
        .S({\result_o[0]_INST_0_i_81_n_0 ,\result_o[0]_INST_0_i_82_n_0 ,\result_o[0]_INST_0_i_83_n_0 ,\result_o[0]_INST_0_i_84_n_0 }));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_61 
       (.I0(b_i[14]),
        .I1(a_i[14]),
        .I2(a_i[15]),
        .I3(b_i[15]),
        .O(\result_o[0]_INST_0_i_61_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_62 
       (.I0(b_i[12]),
        .I1(a_i[12]),
        .I2(a_i[13]),
        .I3(b_i[13]),
        .O(\result_o[0]_INST_0_i_62_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_63 
       (.I0(b_i[10]),
        .I1(a_i[10]),
        .I2(a_i[11]),
        .I3(b_i[11]),
        .O(\result_o[0]_INST_0_i_63_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_64 
       (.I0(b_i[8]),
        .I1(a_i[8]),
        .I2(a_i[9]),
        .I3(b_i[9]),
        .O(\result_o[0]_INST_0_i_64_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_65 
       (.I0(b_i[15]),
        .I1(a_i[15]),
        .I2(b_i[14]),
        .I3(a_i[14]),
        .O(\result_o[0]_INST_0_i_65_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_66 
       (.I0(b_i[13]),
        .I1(a_i[13]),
        .I2(b_i[12]),
        .I3(a_i[12]),
        .O(\result_o[0]_INST_0_i_66_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_67 
       (.I0(b_i[11]),
        .I1(a_i[11]),
        .I2(b_i[10]),
        .I3(a_i[10]),
        .O(\result_o[0]_INST_0_i_67_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_68 
       (.I0(b_i[9]),
        .I1(a_i[9]),
        .I2(b_i[8]),
        .I3(a_i[8]),
        .O(\result_o[0]_INST_0_i_68_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_69 
       (.I0(b_i[6]),
        .I1(a_i[6]),
        .I2(a_i[7]),
        .I3(b_i[7]),
        .O(\result_o[0]_INST_0_i_69_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[0]_INST_0_i_7 
       (.I0(a_i[0]),
        .I1(b_i[0]),
        .O(\result_o[0]_INST_0_i_7_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_70 
       (.I0(b_i[4]),
        .I1(a_i[4]),
        .I2(a_i[5]),
        .I3(b_i[5]),
        .O(\result_o[0]_INST_0_i_70_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_71 
       (.I0(b_i[2]),
        .I1(a_i[2]),
        .I2(a_i[3]),
        .I3(b_i[3]),
        .O(\result_o[0]_INST_0_i_71_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_72 
       (.I0(b_i[0]),
        .I1(a_i[0]),
        .I2(a_i[1]),
        .I3(b_i[1]),
        .O(\result_o[0]_INST_0_i_72_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_73 
       (.I0(b_i[7]),
        .I1(a_i[7]),
        .I2(b_i[6]),
        .I3(a_i[6]),
        .O(\result_o[0]_INST_0_i_73_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_74 
       (.I0(b_i[5]),
        .I1(a_i[5]),
        .I2(b_i[4]),
        .I3(a_i[4]),
        .O(\result_o[0]_INST_0_i_74_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_75 
       (.I0(b_i[3]),
        .I1(a_i[3]),
        .I2(b_i[2]),
        .I3(a_i[2]),
        .O(\result_o[0]_INST_0_i_75_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_76 
       (.I0(b_i[1]),
        .I1(a_i[1]),
        .I2(b_i[0]),
        .I3(a_i[0]),
        .O(\result_o[0]_INST_0_i_76_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_77 
       (.I0(b_i[6]),
        .I1(a_i[6]),
        .I2(a_i[7]),
        .I3(b_i[7]),
        .O(\result_o[0]_INST_0_i_77_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_78 
       (.I0(b_i[4]),
        .I1(a_i[4]),
        .I2(a_i[5]),
        .I3(b_i[5]),
        .O(\result_o[0]_INST_0_i_78_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_79 
       (.I0(b_i[2]),
        .I1(a_i[2]),
        .I2(a_i[3]),
        .I3(b_i[3]),
        .O(\result_o[0]_INST_0_i_79_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT4 #(
    .INIT(16'h0001)) 
    \result_o[0]_INST_0_i_8 
       (.I0(b_i[2]),
        .I1(b_i[1]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .O(\result_o[0]_INST_0_i_8_n_0 ));
  LUT4 #(
    .INIT(16'h2F02)) 
    \result_o[0]_INST_0_i_80 
       (.I0(b_i[0]),
        .I1(a_i[0]),
        .I2(a_i[1]),
        .I3(b_i[1]),
        .O(\result_o[0]_INST_0_i_80_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_81 
       (.I0(b_i[7]),
        .I1(a_i[7]),
        .I2(b_i[6]),
        .I3(a_i[6]),
        .O(\result_o[0]_INST_0_i_81_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_82 
       (.I0(b_i[5]),
        .I1(a_i[5]),
        .I2(b_i[4]),
        .I3(a_i[4]),
        .O(\result_o[0]_INST_0_i_82_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_83 
       (.I0(b_i[3]),
        .I1(a_i[3]),
        .I2(b_i[2]),
        .I3(a_i[2]),
        .O(\result_o[0]_INST_0_i_83_n_0 ));
  LUT4 #(
    .INIT(16'h9009)) 
    \result_o[0]_INST_0_i_84 
       (.I0(b_i[1]),
        .I1(a_i[1]),
        .I2(b_i[0]),
        .I3(a_i[0]),
        .O(\result_o[0]_INST_0_i_84_n_0 ));
  LUT6 #(
    .INIT(64'hF0F0F0F0FFF8F8F8)) 
    \result_o[0]_INST_0_i_9 
       (.I0(a_i[0]),
        .I1(\result_o[0]_INST_0_i_8_n_0 ),
        .I2(\result_o[0]_INST_0_i_14_n_0 ),
        .I3(\result_o[4]_INST_0_i_10_n_0 ),
        .I4(\result_o[31]_INST_0_i_25_n_0 ),
        .I5(b_i[0]),
        .O(\result_o[0]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[10]_INST_0 
       (.I0(\result_o[10]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[10]_INST_0_i_2_n_0 ),
        .I3(\result_o[10]_INST_0_i_3_n_0 ),
        .I4(\result_o[10]_INST_0_i_4_n_0 ),
        .I5(\result_o[10]_INST_0_i_5_n_0 ),
        .O(result_o[10]));
  (* SOFT_HLUTNM = "soft_lutpair39" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[10]_INST_0_i_1 
       (.I0(\result_o[11]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[10]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[10]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFF00AAAACCCCF0F0)) 
    \result_o[10]_INST_0_i_10 
       (.I0(a_i[26]),
        .I1(a_i[18]),
        .I2(a_i[10]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[10]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[10]_INST_0_i_11 
       (.I0(a_i[3]),
        .I1(a_i[5]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[10]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair13" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[10]_INST_0_i_12 
       (.I0(a_i[10]),
        .I1(b_i[4]),
        .I2(b_i[3]),
        .I3(a_i[18]),
        .I4(a_i[26]),
        .O(\result_o[10]_INST_0_i_12_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[10]_INST_0_i_2 
       (.I0(\result_o[10]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[11]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[10]_INST_0_i_8_n_0 ),
        .O(\result_o[10]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[10]_INST_0_i_3 
       (.I0(data0[10]),
        .I1(a_i[10]),
        .I2(b_i[10]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[10]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[10]_INST_0_i_4 
       (.I0(\result_o[11]_INST_0_i_10_n_0 ),
        .I1(\result_o[10]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[10]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[10]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[10]),
        .O(\result_o[10]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[10]_INST_0_i_6 
       (.I0(\result_o[14]_INST_0_i_10_n_0 ),
        .I1(\result_o[16]_INST_0_i_9_n_0 ),
        .I2(\result_o[10]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[12]_INST_0_i_10_n_0 ),
        .O(\result_o[10]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[10]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[10]),
        .I4(b_i[10]),
        .O(\result_o[10]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hAAAEAFAEAAAEAAAE)) 
    \result_o[10]_INST_0_i_8 
       (.I0(\result_o[10]_INST_0_i_11_n_0 ),
        .I1(\result_o[16]_INST_0_i_11_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[30]_INST_0_i_9_n_0 ),
        .I5(a_i[7]),
        .O(\result_o[10]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[10]_INST_0_i_9 
       (.I0(\result_o[14]_INST_0_i_12_n_0 ),
        .I1(\result_o[16]_INST_0_i_10_n_0 ),
        .I2(\result_o[10]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[12]_INST_0_i_12_n_0 ),
        .O(\result_o[10]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[11]_INST_0 
       (.I0(\result_o[11]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[11]_INST_0_i_2_n_0 ),
        .I3(\result_o[11]_INST_0_i_3_n_0 ),
        .I4(\result_o[11]_INST_0_i_4_n_0 ),
        .I5(\result_o[11]_INST_0_i_5_n_0 ),
        .O(result_o[11]));
  (* SOFT_HLUTNM = "soft_lutpair39" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[11]_INST_0_i_1 
       (.I0(\result_o[12]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[11]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[11]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[11]_INST_0_i_10 
       (.I0(\result_o[15]_INST_0_i_18_n_0 ),
        .I1(\result_o[17]_INST_0_i_10_n_0 ),
        .I2(\result_o[11]_INST_0_i_18_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[13]_INST_0_i_12_n_0 ),
        .O(\result_o[11]_INST_0_i_10_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[11]_INST_0_i_11 
       (.CI(\result_o[7]_INST_0_i_11_n_0 ),
        .CO({\result_o[11]_INST_0_i_11_n_0 ,\result_o[11]_INST_0_i_11_n_1 ,\result_o[11]_INST_0_i_11_n_2 ,\result_o[11]_INST_0_i_11_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[11:8]),
        .O(data1[11:8]),
        .S({\result_o[11]_INST_0_i_19_n_0 ,\result_o[11]_INST_0_i_20_n_0 ,\result_o[11]_INST_0_i_21_n_0 ,\result_o[11]_INST_0_i_22_n_0 }));
  LUT6 #(
    .INIT(64'hFF00AAAACCCCF0F0)) 
    \result_o[11]_INST_0_i_12 
       (.I0(a_i[27]),
        .I1(a_i[19]),
        .I2(a_i[11]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[11]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[11]_INST_0_i_13 
       (.I0(a_i[4]),
        .I1(a_i[6]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[11]_INST_0_i_13_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[11]_INST_0_i_14 
       (.I0(a_i[11]),
        .I1(b_i[11]),
        .O(\result_o[11]_INST_0_i_14_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[11]_INST_0_i_15 
       (.I0(a_i[10]),
        .I1(b_i[10]),
        .O(\result_o[11]_INST_0_i_15_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[11]_INST_0_i_16 
       (.I0(a_i[9]),
        .I1(b_i[9]),
        .O(\result_o[11]_INST_0_i_16_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[11]_INST_0_i_17 
       (.I0(a_i[8]),
        .I1(b_i[8]),
        .O(\result_o[11]_INST_0_i_17_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair14" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[11]_INST_0_i_18 
       (.I0(a_i[11]),
        .I1(b_i[4]),
        .I2(b_i[3]),
        .I3(a_i[19]),
        .I4(a_i[27]),
        .O(\result_o[11]_INST_0_i_18_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[11]_INST_0_i_19 
       (.I0(b_i[11]),
        .I1(a_i[11]),
        .O(\result_o[11]_INST_0_i_19_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[11]_INST_0_i_2 
       (.I0(\result_o[11]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[12]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[11]_INST_0_i_8_n_0 ),
        .O(\result_o[11]_INST_0_i_2_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[11]_INST_0_i_20 
       (.I0(b_i[10]),
        .I1(a_i[10]),
        .O(\result_o[11]_INST_0_i_20_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[11]_INST_0_i_21 
       (.I0(b_i[9]),
        .I1(a_i[9]),
        .O(\result_o[11]_INST_0_i_21_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[11]_INST_0_i_22 
       (.I0(b_i[8]),
        .I1(a_i[8]),
        .O(\result_o[11]_INST_0_i_22_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[11]_INST_0_i_3 
       (.I0(data0[11]),
        .I1(a_i[11]),
        .I2(b_i[11]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[11]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[11]_INST_0_i_4 
       (.I0(\result_o[12]_INST_0_i_9_n_0 ),
        .I1(\result_o[11]_INST_0_i_10_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[11]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[11]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[11]),
        .O(\result_o[11]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[11]_INST_0_i_6 
       (.I0(\result_o[15]_INST_0_i_12_n_0 ),
        .I1(\result_o[17]_INST_0_i_9_n_0 ),
        .I2(\result_o[11]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[13]_INST_0_i_10_n_0 ),
        .O(\result_o[11]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[11]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[11]),
        .I4(b_i[11]),
        .O(\result_o[11]_INST_0_i_7_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT5 #(
    .INIT(32'hAFAEAAAE)) 
    \result_o[11]_INST_0_i_8 
       (.I0(\result_o[11]_INST_0_i_13_n_0 ),
        .I1(\result_o[17]_INST_0_i_11_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[15]_INST_0_i_13_n_0 ),
        .O(\result_o[11]_INST_0_i_8_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[11]_INST_0_i_9 
       (.CI(\result_o[7]_INST_0_i_9_n_0 ),
        .CO({\result_o[11]_INST_0_i_9_n_0 ,\result_o[11]_INST_0_i_9_n_1 ,\result_o[11]_INST_0_i_9_n_2 ,\result_o[11]_INST_0_i_9_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[11:8]),
        .O(data0[11:8]),
        .S({\result_o[11]_INST_0_i_14_n_0 ,\result_o[11]_INST_0_i_15_n_0 ,\result_o[11]_INST_0_i_16_n_0 ,\result_o[11]_INST_0_i_17_n_0 }));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[12]_INST_0 
       (.I0(\result_o[12]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[12]_INST_0_i_2_n_0 ),
        .I3(\result_o[12]_INST_0_i_3_n_0 ),
        .I4(\result_o[12]_INST_0_i_4_n_0 ),
        .I5(\result_o[12]_INST_0_i_5_n_0 ),
        .O(result_o[12]));
  (* SOFT_HLUTNM = "soft_lutpair40" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[12]_INST_0_i_1 
       (.I0(\result_o[13]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[12]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[12]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFF00AAAACCCCF0F0)) 
    \result_o[12]_INST_0_i_10 
       (.I0(a_i[28]),
        .I1(a_i[20]),
        .I2(a_i[12]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[12]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[12]_INST_0_i_11 
       (.I0(a_i[5]),
        .I1(a_i[7]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[12]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair15" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[12]_INST_0_i_12 
       (.I0(a_i[12]),
        .I1(b_i[4]),
        .I2(b_i[3]),
        .I3(a_i[20]),
        .I4(a_i[28]),
        .O(\result_o[12]_INST_0_i_12_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[12]_INST_0_i_2 
       (.I0(\result_o[12]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[13]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[12]_INST_0_i_8_n_0 ),
        .O(\result_o[12]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[12]_INST_0_i_3 
       (.I0(data0[12]),
        .I1(a_i[12]),
        .I2(b_i[12]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[12]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[12]_INST_0_i_4 
       (.I0(\result_o[13]_INST_0_i_9_n_0 ),
        .I1(\result_o[12]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[12]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[12]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[12]),
        .O(\result_o[12]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[12]_INST_0_i_6 
       (.I0(\result_o[16]_INST_0_i_9_n_0 ),
        .I1(\result_o[18]_INST_0_i_9_n_0 ),
        .I2(\result_o[12]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[14]_INST_0_i_10_n_0 ),
        .O(\result_o[12]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[12]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[12]),
        .I4(b_i[12]),
        .O(\result_o[12]_INST_0_i_7_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT5 #(
    .INIT(32'hAFAEAAAE)) 
    \result_o[12]_INST_0_i_8 
       (.I0(\result_o[12]_INST_0_i_11_n_0 ),
        .I1(\result_o[18]_INST_0_i_12_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[16]_INST_0_i_11_n_0 ),
        .O(\result_o[12]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[12]_INST_0_i_9 
       (.I0(\result_o[16]_INST_0_i_10_n_0 ),
        .I1(\result_o[18]_INST_0_i_11_n_0 ),
        .I2(\result_o[12]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[14]_INST_0_i_12_n_0 ),
        .O(\result_o[12]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[13]_INST_0 
       (.I0(\result_o[13]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[13]_INST_0_i_2_n_0 ),
        .I3(\result_o[13]_INST_0_i_3_n_0 ),
        .I4(\result_o[13]_INST_0_i_4_n_0 ),
        .I5(\result_o[13]_INST_0_i_5_n_0 ),
        .O(result_o[13]));
  (* SOFT_HLUTNM = "soft_lutpair40" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[13]_INST_0_i_1 
       (.I0(\result_o[14]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[13]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[13]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFF00AAAACCCCF0F0)) 
    \result_o[13]_INST_0_i_10 
       (.I0(a_i[29]),
        .I1(a_i[21]),
        .I2(a_i[13]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[13]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair6" *) 
  LUT5 #(
    .INIT(32'h10000000)) 
    \result_o[13]_INST_0_i_11 
       (.I0(b_i[3]),
        .I1(b_i[4]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[6]),
        .O(\result_o[13]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair16" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[13]_INST_0_i_12 
       (.I0(a_i[13]),
        .I1(b_i[4]),
        .I2(b_i[3]),
        .I3(a_i[21]),
        .I4(a_i[29]),
        .O(\result_o[13]_INST_0_i_12_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[13]_INST_0_i_2 
       (.I0(\result_o[13]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[14]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[13]_INST_0_i_8_n_0 ),
        .O(\result_o[13]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[13]_INST_0_i_3 
       (.I0(data0[13]),
        .I1(a_i[13]),
        .I2(b_i[13]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[13]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[13]_INST_0_i_4 
       (.I0(\result_o[14]_INST_0_i_9_n_0 ),
        .I1(\result_o[13]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[13]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[13]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[13]),
        .O(\result_o[13]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[13]_INST_0_i_6 
       (.I0(\result_o[17]_INST_0_i_9_n_0 ),
        .I1(\result_o[19]_INST_0_i_11_n_0 ),
        .I2(\result_o[13]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[15]_INST_0_i_12_n_0 ),
        .O(\result_o[13]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[13]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[13]),
        .I4(b_i[13]),
        .O(\result_o[13]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFEEFCCCCCEEFC)) 
    \result_o[13]_INST_0_i_8 
       (.I0(\result_o[15]_INST_0_i_13_n_0 ),
        .I1(\result_o[13]_INST_0_i_11_n_0 ),
        .I2(\result_o[19]_INST_0_i_14_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[17]_INST_0_i_11_n_0 ),
        .O(\result_o[13]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[13]_INST_0_i_9 
       (.I0(\result_o[17]_INST_0_i_10_n_0 ),
        .I1(\result_o[19]_INST_0_i_13_n_0 ),
        .I2(\result_o[13]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[15]_INST_0_i_18_n_0 ),
        .O(\result_o[13]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[14]_INST_0 
       (.I0(\result_o[14]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[14]_INST_0_i_2_n_0 ),
        .I3(\result_o[14]_INST_0_i_3_n_0 ),
        .I4(\result_o[14]_INST_0_i_4_n_0 ),
        .I5(\result_o[14]_INST_0_i_5_n_0 ),
        .O(result_o[14]));
  (* SOFT_HLUTNM = "soft_lutpair41" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[14]_INST_0_i_1 
       (.I0(\result_o[15]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[14]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[14]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFF00CCCCAAAAF0F0)) 
    \result_o[14]_INST_0_i_10 
       (.I0(a_i[22]),
        .I1(a_i[30]),
        .I2(a_i[14]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[14]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair7" *) 
  LUT5 #(
    .INIT(32'h10000000)) 
    \result_o[14]_INST_0_i_11 
       (.I0(b_i[3]),
        .I1(b_i[4]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[7]),
        .O(\result_o[14]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair17" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[14]_INST_0_i_12 
       (.I0(a_i[14]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[30]),
        .I4(a_i[22]),
        .O(\result_o[14]_INST_0_i_12_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[14]_INST_0_i_2 
       (.I0(\result_o[14]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[15]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[14]_INST_0_i_8_n_0 ),
        .O(\result_o[14]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[14]_INST_0_i_3 
       (.I0(data0[14]),
        .I1(a_i[14]),
        .I2(b_i[14]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[14]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[14]_INST_0_i_4 
       (.I0(\result_o[15]_INST_0_i_10_n_0 ),
        .I1(\result_o[14]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[14]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[14]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[14]),
        .O(\result_o[14]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[14]_INST_0_i_6 
       (.I0(\result_o[18]_INST_0_i_9_n_0 ),
        .I1(\result_o[20]_INST_0_i_9_n_0 ),
        .I2(\result_o[14]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[16]_INST_0_i_9_n_0 ),
        .O(\result_o[14]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[14]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[14]),
        .I4(b_i[14]),
        .O(\result_o[14]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFEEFCCCCCEEFC)) 
    \result_o[14]_INST_0_i_8 
       (.I0(\result_o[16]_INST_0_i_11_n_0 ),
        .I1(\result_o[14]_INST_0_i_11_n_0 ),
        .I2(\result_o[20]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[18]_INST_0_i_12_n_0 ),
        .O(\result_o[14]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[14]_INST_0_i_9 
       (.I0(\result_o[18]_INST_0_i_11_n_0 ),
        .I1(\result_o[20]_INST_0_i_11_n_0 ),
        .I2(\result_o[14]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[16]_INST_0_i_10_n_0 ),
        .O(\result_o[14]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[15]_INST_0 
       (.I0(\result_o[15]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[15]_INST_0_i_2_n_0 ),
        .I3(\result_o[15]_INST_0_i_3_n_0 ),
        .I4(\result_o[15]_INST_0_i_4_n_0 ),
        .I5(\result_o[15]_INST_0_i_5_n_0 ),
        .O(result_o[15]));
  (* SOFT_HLUTNM = "soft_lutpair41" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[15]_INST_0_i_1 
       (.I0(\result_o[16]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[15]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[15]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[15]_INST_0_i_10 
       (.I0(\result_o[19]_INST_0_i_13_n_0 ),
        .I1(\result_o[21]_INST_0_i_11_n_0 ),
        .I2(\result_o[15]_INST_0_i_18_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[17]_INST_0_i_10_n_0 ),
        .O(\result_o[15]_INST_0_i_10_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[15]_INST_0_i_11 
       (.CI(\result_o[11]_INST_0_i_11_n_0 ),
        .CO({\result_o[15]_INST_0_i_11_n_0 ,\result_o[15]_INST_0_i_11_n_1 ,\result_o[15]_INST_0_i_11_n_2 ,\result_o[15]_INST_0_i_11_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[15:12]),
        .O(data1[15:12]),
        .S({\result_o[15]_INST_0_i_19_n_0 ,\result_o[15]_INST_0_i_20_n_0 ,\result_o[15]_INST_0_i_21_n_0 ,\result_o[15]_INST_0_i_22_n_0 }));
  (* SOFT_HLUTNM = "soft_lutpair18" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[15]_INST_0_i_12 
       (.I0(a_i[15]),
        .I1(b_i[3]),
        .I2(a_i[23]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[15]_INST_0_i_12_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair20" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[15]_INST_0_i_13 
       (.I0(a_i[0]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[8]),
        .O(\result_o[15]_INST_0_i_13_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[15]_INST_0_i_14 
       (.I0(a_i[15]),
        .I1(b_i[15]),
        .O(\result_o[15]_INST_0_i_14_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[15]_INST_0_i_15 
       (.I0(a_i[14]),
        .I1(b_i[14]),
        .O(\result_o[15]_INST_0_i_15_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[15]_INST_0_i_16 
       (.I0(a_i[13]),
        .I1(b_i[13]),
        .O(\result_o[15]_INST_0_i_16_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[15]_INST_0_i_17 
       (.I0(a_i[12]),
        .I1(b_i[12]),
        .O(\result_o[15]_INST_0_i_17_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair18" *) 
  LUT5 #(
    .INIT(32'h0FAC00AC)) 
    \result_o[15]_INST_0_i_18 
       (.I0(a_i[31]),
        .I1(a_i[15]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(a_i[23]),
        .O(\result_o[15]_INST_0_i_18_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[15]_INST_0_i_19 
       (.I0(b_i[15]),
        .I1(a_i[15]),
        .O(\result_o[15]_INST_0_i_19_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[15]_INST_0_i_2 
       (.I0(\result_o[15]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[16]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[15]_INST_0_i_8_n_0 ),
        .O(\result_o[15]_INST_0_i_2_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[15]_INST_0_i_20 
       (.I0(b_i[14]),
        .I1(a_i[14]),
        .O(\result_o[15]_INST_0_i_20_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[15]_INST_0_i_21 
       (.I0(b_i[13]),
        .I1(a_i[13]),
        .O(\result_o[15]_INST_0_i_21_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[15]_INST_0_i_22 
       (.I0(b_i[12]),
        .I1(a_i[12]),
        .O(\result_o[15]_INST_0_i_22_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[15]_INST_0_i_3 
       (.I0(data0[15]),
        .I1(a_i[15]),
        .I2(b_i[15]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[15]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[15]_INST_0_i_4 
       (.I0(\result_o[16]_INST_0_i_7_n_0 ),
        .I1(\result_o[15]_INST_0_i_10_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[15]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[15]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[15]),
        .O(\result_o[15]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[15]_INST_0_i_6 
       (.I0(\result_o[19]_INST_0_i_11_n_0 ),
        .I1(\result_o[21]_INST_0_i_9_n_0 ),
        .I2(\result_o[15]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[17]_INST_0_i_9_n_0 ),
        .O(\result_o[15]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[15]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[15]),
        .I4(b_i[15]),
        .O(\result_o[15]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[15]_INST_0_i_8 
       (.I0(\result_o[17]_INST_0_i_11_n_0 ),
        .I1(\result_o[15]_INST_0_i_13_n_0 ),
        .I2(\result_o[21]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[19]_INST_0_i_14_n_0 ),
        .O(\result_o[15]_INST_0_i_8_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[15]_INST_0_i_9 
       (.CI(\result_o[11]_INST_0_i_9_n_0 ),
        .CO({\result_o[15]_INST_0_i_9_n_0 ,\result_o[15]_INST_0_i_9_n_1 ,\result_o[15]_INST_0_i_9_n_2 ,\result_o[15]_INST_0_i_9_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[15:12]),
        .O(data0[15:12]),
        .S({\result_o[15]_INST_0_i_14_n_0 ,\result_o[15]_INST_0_i_15_n_0 ,\result_o[15]_INST_0_i_16_n_0 ,\result_o[15]_INST_0_i_17_n_0 }));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[16]_INST_0 
       (.I0(\result_o[16]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[16]_INST_0_i_2_n_0 ),
        .I3(\result_o[16]_INST_0_i_3_n_0 ),
        .I4(\result_o[16]_INST_0_i_4_n_0 ),
        .I5(\result_o[16]_INST_0_i_5_n_0 ),
        .O(result_o[16]));
  (* SOFT_HLUTNM = "soft_lutpair42" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[16]_INST_0_i_1 
       (.I0(\result_o[17]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[16]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[16]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair11" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[16]_INST_0_i_10 
       (.I0(a_i[24]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[16]),
        .O(\result_o[16]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair22" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[16]_INST_0_i_11 
       (.I0(a_i[1]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[9]),
        .O(\result_o[16]_INST_0_i_11_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[16]_INST_0_i_2 
       (.I0(\result_o[17]_INST_0_i_7_n_0 ),
        .I1(\result_o[16]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[16]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[16]_INST_0_i_3 
       (.I0(\result_o[16]_INST_0_i_8_n_0 ),
        .I1(\result_o[17]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[16]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[16]_INST_0_i_4 
       (.I0(data0[16]),
        .I1(b_i[16]),
        .I2(a_i[16]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[16]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[16]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[16]),
        .O(\result_o[16]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[16]_INST_0_i_6 
       (.I0(\result_o[20]_INST_0_i_9_n_0 ),
        .I1(\result_o[22]_INST_0_i_9_n_0 ),
        .I2(\result_o[16]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[18]_INST_0_i_9_n_0 ),
        .O(\result_o[16]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[16]_INST_0_i_7 
       (.I0(\result_o[20]_INST_0_i_11_n_0 ),
        .I1(\result_o[22]_INST_0_i_11_n_0 ),
        .I2(\result_o[16]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[18]_INST_0_i_11_n_0 ),
        .O(\result_o[16]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[16]_INST_0_i_8 
       (.I0(\result_o[18]_INST_0_i_12_n_0 ),
        .I1(\result_o[16]_INST_0_i_11_n_0 ),
        .I2(\result_o[22]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[20]_INST_0_i_12_n_0 ),
        .O(\result_o[16]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair19" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[16]_INST_0_i_9 
       (.I0(a_i[16]),
        .I1(b_i[3]),
        .I2(a_i[24]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[16]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[17]_INST_0 
       (.I0(\result_o[17]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[17]_INST_0_i_2_n_0 ),
        .I3(\result_o[17]_INST_0_i_3_n_0 ),
        .I4(\result_o[17]_INST_0_i_4_n_0 ),
        .I5(\result_o[17]_INST_0_i_5_n_0 ),
        .O(result_o[17]));
  (* SOFT_HLUTNM = "soft_lutpair42" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[17]_INST_0_i_1 
       (.I0(\result_o[18]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[17]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[17]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair12" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[17]_INST_0_i_10 
       (.I0(a_i[25]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[17]),
        .O(\result_o[17]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair24" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[17]_INST_0_i_11 
       (.I0(a_i[2]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[10]),
        .O(\result_o[17]_INST_0_i_11_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[17]_INST_0_i_2 
       (.I0(\result_o[18]_INST_0_i_7_n_0 ),
        .I1(\result_o[17]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[17]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[17]_INST_0_i_3 
       (.I0(\result_o[17]_INST_0_i_8_n_0 ),
        .I1(\result_o[18]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[17]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[17]_INST_0_i_4 
       (.I0(data0[17]),
        .I1(b_i[17]),
        .I2(a_i[17]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[17]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[17]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[17]),
        .O(\result_o[17]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[17]_INST_0_i_6 
       (.I0(\result_o[21]_INST_0_i_9_n_0 ),
        .I1(\result_o[23]_INST_0_i_10_n_0 ),
        .I2(\result_o[17]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[19]_INST_0_i_11_n_0 ),
        .O(\result_o[17]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[17]_INST_0_i_7 
       (.I0(\result_o[21]_INST_0_i_11_n_0 ),
        .I1(\result_o[23]_INST_0_i_12_n_0 ),
        .I2(\result_o[17]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[19]_INST_0_i_13_n_0 ),
        .O(\result_o[17]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[17]_INST_0_i_8 
       (.I0(\result_o[19]_INST_0_i_14_n_0 ),
        .I1(\result_o[17]_INST_0_i_11_n_0 ),
        .I2(\result_o[23]_INST_0_i_13_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[21]_INST_0_i_12_n_0 ),
        .O(\result_o[17]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair21" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[17]_INST_0_i_9 
       (.I0(a_i[17]),
        .I1(b_i[3]),
        .I2(a_i[25]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[17]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[18]_INST_0 
       (.I0(\result_o[18]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[18]_INST_0_i_2_n_0 ),
        .I3(\result_o[18]_INST_0_i_3_n_0 ),
        .I4(\result_o[18]_INST_0_i_4_n_0 ),
        .I5(\result_o[18]_INST_0_i_5_n_0 ),
        .O(result_o[18]));
  (* SOFT_HLUTNM = "soft_lutpair43" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[18]_INST_0_i_1 
       (.I0(\result_o[19]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[18]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[18]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair8" *) 
  LUT5 #(
    .INIT(32'h10000000)) 
    \result_o[18]_INST_0_i_10 
       (.I0(b_i[3]),
        .I1(b_i[4]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[24]),
        .O(\result_o[18]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair13" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[18]_INST_0_i_11 
       (.I0(a_i[26]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[18]),
        .O(\result_o[18]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair26" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[18]_INST_0_i_12 
       (.I0(a_i[3]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[11]),
        .O(\result_o[18]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[18]_INST_0_i_2 
       (.I0(\result_o[19]_INST_0_i_7_n_0 ),
        .I1(\result_o[18]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[18]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[18]_INST_0_i_3 
       (.I0(\result_o[18]_INST_0_i_8_n_0 ),
        .I1(\result_o[19]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[18]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[18]_INST_0_i_4 
       (.I0(data0[18]),
        .I1(b_i[18]),
        .I2(a_i[18]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[18]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[18]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[18]),
        .O(\result_o[18]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[18]_INST_0_i_6 
       (.I0(\result_o[22]_INST_0_i_9_n_0 ),
        .I1(\result_o[24]_INST_0_i_9_n_0 ),
        .I2(\result_o[18]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[20]_INST_0_i_9_n_0 ),
        .O(\result_o[18]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFEEFCCCCCEEFC)) 
    \result_o[18]_INST_0_i_7 
       (.I0(\result_o[22]_INST_0_i_11_n_0 ),
        .I1(\result_o[18]_INST_0_i_10_n_0 ),
        .I2(\result_o[18]_INST_0_i_11_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[20]_INST_0_i_11_n_0 ),
        .O(\result_o[18]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[18]_INST_0_i_8 
       (.I0(\result_o[20]_INST_0_i_12_n_0 ),
        .I1(\result_o[18]_INST_0_i_12_n_0 ),
        .I2(\result_o[24]_INST_0_i_11_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[22]_INST_0_i_12_n_0 ),
        .O(\result_o[18]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair23" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[18]_INST_0_i_9 
       (.I0(a_i[18]),
        .I1(b_i[3]),
        .I2(a_i[26]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[18]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[19]_INST_0 
       (.I0(\result_o[19]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[19]_INST_0_i_2_n_0 ),
        .I3(\result_o[19]_INST_0_i_3_n_0 ),
        .I4(\result_o[19]_INST_0_i_4_n_0 ),
        .I5(\result_o[19]_INST_0_i_5_n_0 ),
        .O(result_o[19]));
  (* SOFT_HLUTNM = "soft_lutpair43" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[19]_INST_0_i_1 
       (.I0(\result_o[20]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[19]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[19]_INST_0_i_1_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[19]_INST_0_i_10 
       (.CI(\result_o[15]_INST_0_i_11_n_0 ),
        .CO({\result_o[19]_INST_0_i_10_n_0 ,\result_o[19]_INST_0_i_10_n_1 ,\result_o[19]_INST_0_i_10_n_2 ,\result_o[19]_INST_0_i_10_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[19:16]),
        .O(data1[19:16]),
        .S({\result_o[19]_INST_0_i_19_n_0 ,\result_o[19]_INST_0_i_20_n_0 ,\result_o[19]_INST_0_i_21_n_0 ,\result_o[19]_INST_0_i_22_n_0 }));
  (* SOFT_HLUTNM = "soft_lutpair25" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[19]_INST_0_i_11 
       (.I0(a_i[19]),
        .I1(b_i[3]),
        .I2(a_i[27]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[19]_INST_0_i_11_n_0 ));
  LUT5 #(
    .INIT(32'h10000000)) 
    \result_o[19]_INST_0_i_12 
       (.I0(b_i[3]),
        .I1(b_i[4]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[25]),
        .O(\result_o[19]_INST_0_i_12_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair14" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[19]_INST_0_i_13 
       (.I0(a_i[27]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[19]),
        .O(\result_o[19]_INST_0_i_13_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair28" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[19]_INST_0_i_14 
       (.I0(a_i[4]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[12]),
        .O(\result_o[19]_INST_0_i_14_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[19]_INST_0_i_15 
       (.I0(a_i[19]),
        .I1(b_i[19]),
        .O(\result_o[19]_INST_0_i_15_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[19]_INST_0_i_16 
       (.I0(a_i[18]),
        .I1(b_i[18]),
        .O(\result_o[19]_INST_0_i_16_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[19]_INST_0_i_17 
       (.I0(a_i[17]),
        .I1(b_i[17]),
        .O(\result_o[19]_INST_0_i_17_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[19]_INST_0_i_18 
       (.I0(a_i[16]),
        .I1(b_i[16]),
        .O(\result_o[19]_INST_0_i_18_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[19]_INST_0_i_19 
       (.I0(b_i[19]),
        .I1(a_i[19]),
        .O(\result_o[19]_INST_0_i_19_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[19]_INST_0_i_2 
       (.I0(\result_o[20]_INST_0_i_7_n_0 ),
        .I1(\result_o[19]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[19]_INST_0_i_2_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[19]_INST_0_i_20 
       (.I0(b_i[18]),
        .I1(a_i[18]),
        .O(\result_o[19]_INST_0_i_20_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[19]_INST_0_i_21 
       (.I0(b_i[17]),
        .I1(a_i[17]),
        .O(\result_o[19]_INST_0_i_21_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[19]_INST_0_i_22 
       (.I0(b_i[16]),
        .I1(a_i[16]),
        .O(\result_o[19]_INST_0_i_22_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[19]_INST_0_i_3 
       (.I0(\result_o[19]_INST_0_i_8_n_0 ),
        .I1(\result_o[20]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[19]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[19]_INST_0_i_4 
       (.I0(data0[19]),
        .I1(b_i[19]),
        .I2(a_i[19]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[19]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[19]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[19]),
        .O(\result_o[19]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[19]_INST_0_i_6 
       (.I0(\result_o[23]_INST_0_i_10_n_0 ),
        .I1(\result_o[25]_INST_0_i_9_n_0 ),
        .I2(\result_o[19]_INST_0_i_11_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[21]_INST_0_i_9_n_0 ),
        .O(\result_o[19]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFEEFCCCCCEEFC)) 
    \result_o[19]_INST_0_i_7 
       (.I0(\result_o[23]_INST_0_i_12_n_0 ),
        .I1(\result_o[19]_INST_0_i_12_n_0 ),
        .I2(\result_o[19]_INST_0_i_13_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[21]_INST_0_i_11_n_0 ),
        .O(\result_o[19]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[19]_INST_0_i_8 
       (.I0(\result_o[21]_INST_0_i_12_n_0 ),
        .I1(\result_o[19]_INST_0_i_14_n_0 ),
        .I2(\result_o[25]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[23]_INST_0_i_13_n_0 ),
        .O(\result_o[19]_INST_0_i_8_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[19]_INST_0_i_9 
       (.CI(\result_o[15]_INST_0_i_9_n_0 ),
        .CO({\result_o[19]_INST_0_i_9_n_0 ,\result_o[19]_INST_0_i_9_n_1 ,\result_o[19]_INST_0_i_9_n_2 ,\result_o[19]_INST_0_i_9_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[19:16]),
        .O(data0[19:16]),
        .S({\result_o[19]_INST_0_i_15_n_0 ,\result_o[19]_INST_0_i_16_n_0 ,\result_o[19]_INST_0_i_17_n_0 ,\result_o[19]_INST_0_i_18_n_0 }));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[1]_INST_0 
       (.I0(\result_o[1]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[1]_INST_0_i_2_n_0 ),
        .I3(\result_o[1]_INST_0_i_3_n_0 ),
        .I4(\result_o[1]_INST_0_i_4_n_0 ),
        .I5(\result_o[1]_INST_0_i_5_n_0 ),
        .O(result_o[1]));
  LUT6 #(
    .INIT(64'hFFFFFFE0E0E0E0E0)) 
    \result_o[1]_INST_0_i_1 
       (.I0(\result_o[2]_INST_0_i_7_n_0 ),
        .I1(\result_o[2]_INST_0_i_8_n_0 ),
        .I2(\result_o[30]_INST_0_i_7_n_0 ),
        .I3(\result_o[1]_INST_0_i_6_n_0 ),
        .I4(\result_o[1]_INST_0_i_7_n_0 ),
        .I5(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[1]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFF08080800)) 
    \result_o[1]_INST_0_i_2 
       (.I0(alu_op_i[1]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[0]),
        .I3(a_i[1]),
        .I4(b_i[1]),
        .I5(\result_o[1]_INST_0_i_8_n_0 ),
        .O(\result_o[1]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hC1C0454445440100)) 
    \result_o[1]_INST_0_i_3 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(data0[1]),
        .I4(a_i[1]),
        .I5(b_i[1]),
        .O(\result_o[1]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFE0E0E0E0E0)) 
    \result_o[1]_INST_0_i_4 
       (.I0(\result_o[2]_INST_0_i_12_n_0 ),
        .I1(\result_o[2]_INST_0_i_8_n_0 ),
        .I2(\result_o[30]_INST_0_i_11_n_0 ),
        .I3(\result_o[1]_INST_0_i_6_n_0 ),
        .I4(\result_o[1]_INST_0_i_7_n_0 ),
        .I5(\result_o[30]_INST_0_i_12_n_0 ),
        .O(\result_o[1]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[1]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[1]),
        .O(\result_o[1]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hEEEEEEEEEEEEEAAA)) 
    \result_o[1]_INST_0_i_6 
       (.I0(\result_o[1]_INST_0_i_9_n_0 ),
        .I1(b_i[1]),
        .I2(\result_o[7]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(\result_o[3]_INST_0_i_13_n_0 ),
        .I5(\result_o[3]_INST_0_i_14_n_0 ),
        .O(\result_o[1]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFF888F888F888)) 
    \result_o[1]_INST_0_i_7 
       (.I0(\result_o[0]_INST_0_i_8_n_0 ),
        .I1(a_i[1]),
        .I2(\result_o[31]_INST_0_i_23_n_0 ),
        .I3(a_i[9]),
        .I4(\result_o[5]_INST_0_i_10_n_0 ),
        .I5(\result_o[31]_INST_0_i_25_n_0 ),
        .O(\result_o[1]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h000000F800000088)) 
    \result_o[1]_INST_0_i_8 
       (.I0(\result_o[30]_INST_0_i_15_n_0 ),
        .I1(a_i[0]),
        .I2(\result_o[31]_INST_0_i_11_n_0 ),
        .I3(\result_o[30]_INST_0_i_9_n_0 ),
        .I4(\result_o[30]_INST_0_i_8_n_0 ),
        .I5(a_i[1]),
        .O(\result_o[1]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[1]_INST_0_i_9 
       (.I0(a_i[25]),
        .I1(a_i[17]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .I5(b_i[1]),
        .O(\result_o[1]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[20]_INST_0 
       (.I0(\result_o[20]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[20]_INST_0_i_2_n_0 ),
        .I3(\result_o[20]_INST_0_i_3_n_0 ),
        .I4(\result_o[20]_INST_0_i_4_n_0 ),
        .I5(\result_o[20]_INST_0_i_5_n_0 ),
        .O(result_o[20]));
  (* SOFT_HLUTNM = "soft_lutpair44" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[20]_INST_0_i_1 
       (.I0(\result_o[21]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[20]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[20]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[20]_INST_0_i_10 
       (.I0(a_i[26]),
        .I1(a_i[24]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[20]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair15" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[20]_INST_0_i_11 
       (.I0(a_i[28]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[20]),
        .O(\result_o[20]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair30" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[20]_INST_0_i_12 
       (.I0(a_i[5]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[13]),
        .O(\result_o[20]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[20]_INST_0_i_2 
       (.I0(\result_o[21]_INST_0_i_7_n_0 ),
        .I1(\result_o[20]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[20]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[20]_INST_0_i_3 
       (.I0(\result_o[20]_INST_0_i_8_n_0 ),
        .I1(\result_o[21]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[20]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[20]_INST_0_i_4 
       (.I0(data0[20]),
        .I1(b_i[20]),
        .I2(a_i[20]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[20]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[20]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[20]),
        .O(\result_o[20]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[20]_INST_0_i_6 
       (.I0(\result_o[24]_INST_0_i_9_n_0 ),
        .I1(\result_o[26]_INST_0_i_10_n_0 ),
        .I2(\result_o[20]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[22]_INST_0_i_9_n_0 ),
        .O(\result_o[20]_INST_0_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT5 #(
    .INIT(32'hAFAEAAAE)) 
    \result_o[20]_INST_0_i_7 
       (.I0(\result_o[20]_INST_0_i_10_n_0 ),
        .I1(\result_o[20]_INST_0_i_11_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[22]_INST_0_i_11_n_0 ),
        .O(\result_o[20]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[20]_INST_0_i_8 
       (.I0(\result_o[22]_INST_0_i_12_n_0 ),
        .I1(\result_o[20]_INST_0_i_12_n_0 ),
        .I2(\result_o[26]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[24]_INST_0_i_11_n_0 ),
        .O(\result_o[20]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair27" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[20]_INST_0_i_9 
       (.I0(a_i[20]),
        .I1(b_i[3]),
        .I2(a_i[28]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[20]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[21]_INST_0 
       (.I0(\result_o[21]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[21]_INST_0_i_2_n_0 ),
        .I3(\result_o[21]_INST_0_i_3_n_0 ),
        .I4(\result_o[21]_INST_0_i_4_n_0 ),
        .I5(\result_o[21]_INST_0_i_5_n_0 ),
        .O(result_o[21]));
  (* SOFT_HLUTNM = "soft_lutpair44" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[21]_INST_0_i_1 
       (.I0(\result_o[22]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[21]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[21]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[21]_INST_0_i_10 
       (.I0(a_i[27]),
        .I1(a_i[25]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[21]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair16" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[21]_INST_0_i_11 
       (.I0(a_i[29]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[21]),
        .O(\result_o[21]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair32" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[21]_INST_0_i_12 
       (.I0(a_i[6]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[14]),
        .O(\result_o[21]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[21]_INST_0_i_2 
       (.I0(\result_o[22]_INST_0_i_7_n_0 ),
        .I1(\result_o[21]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[21]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[21]_INST_0_i_3 
       (.I0(\result_o[21]_INST_0_i_8_n_0 ),
        .I1(\result_o[22]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[21]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[21]_INST_0_i_4 
       (.I0(data0[21]),
        .I1(b_i[21]),
        .I2(a_i[21]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[21]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[21]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[21]),
        .O(\result_o[21]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[21]_INST_0_i_6 
       (.I0(\result_o[25]_INST_0_i_9_n_0 ),
        .I1(\result_o[25]_INST_0_i_10_n_0 ),
        .I2(\result_o[21]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[23]_INST_0_i_10_n_0 ),
        .O(\result_o[21]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hAFAEAAAE)) 
    \result_o[21]_INST_0_i_7 
       (.I0(\result_o[21]_INST_0_i_10_n_0 ),
        .I1(\result_o[21]_INST_0_i_11_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[23]_INST_0_i_12_n_0 ),
        .O(\result_o[21]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[21]_INST_0_i_8 
       (.I0(\result_o[23]_INST_0_i_13_n_0 ),
        .I1(\result_o[21]_INST_0_i_12_n_0 ),
        .I2(\result_o[27]_INST_0_i_17_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[25]_INST_0_i_12_n_0 ),
        .O(\result_o[21]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair29" *) 
  LUT5 #(
    .INIT(32'hFF00E2E2)) 
    \result_o[21]_INST_0_i_9 
       (.I0(a_i[21]),
        .I1(b_i[3]),
        .I2(a_i[29]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[21]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[22]_INST_0 
       (.I0(\result_o[22]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[22]_INST_0_i_2_n_0 ),
        .I3(\result_o[22]_INST_0_i_3_n_0 ),
        .I4(\result_o[22]_INST_0_i_4_n_0 ),
        .I5(\result_o[22]_INST_0_i_5_n_0 ),
        .O(result_o[22]));
  (* SOFT_HLUTNM = "soft_lutpair45" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[22]_INST_0_i_1 
       (.I0(\result_o[23]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[22]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[22]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[22]_INST_0_i_10 
       (.I0(a_i[28]),
        .I1(a_i[26]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[22]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair17" *) 
  LUT4 #(
    .INIT(16'h00CA)) 
    \result_o[22]_INST_0_i_11 
       (.I0(a_i[22]),
        .I1(a_i[30]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[22]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair33" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[22]_INST_0_i_12 
       (.I0(a_i[7]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[15]),
        .O(\result_o[22]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[22]_INST_0_i_2 
       (.I0(\result_o[23]_INST_0_i_7_n_0 ),
        .I1(\result_o[22]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[22]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[22]_INST_0_i_3 
       (.I0(\result_o[22]_INST_0_i_8_n_0 ),
        .I1(\result_o[23]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[22]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[22]_INST_0_i_4 
       (.I0(data0[22]),
        .I1(b_i[22]),
        .I2(a_i[22]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[22]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[22]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[22]),
        .O(\result_o[22]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[22]_INST_0_i_6 
       (.I0(\result_o[26]_INST_0_i_10_n_0 ),
        .I1(\result_o[26]_INST_0_i_11_n_0 ),
        .I2(\result_o[22]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[24]_INST_0_i_9_n_0 ),
        .O(\result_o[22]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hAAAEAFAEAAAEAAAE)) 
    \result_o[22]_INST_0_i_7 
       (.I0(\result_o[22]_INST_0_i_10_n_0 ),
        .I1(\result_o[22]_INST_0_i_11_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[30]_INST_0_i_9_n_0 ),
        .I5(a_i[24]),
        .O(\result_o[22]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[22]_INST_0_i_8 
       (.I0(\result_o[24]_INST_0_i_11_n_0 ),
        .I1(\result_o[22]_INST_0_i_12_n_0 ),
        .I2(\result_o[28]_INST_0_i_15_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[26]_INST_0_i_12_n_0 ),
        .O(\result_o[22]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair31" *) 
  LUT5 #(
    .INIT(32'hFF00D8D8)) 
    \result_o[22]_INST_0_i_9 
       (.I0(b_i[3]),
        .I1(a_i[30]),
        .I2(a_i[22]),
        .I3(a_i[31]),
        .I4(b_i[4]),
        .O(\result_o[22]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[23]_INST_0 
       (.I0(\result_o[23]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[23]_INST_0_i_2_n_0 ),
        .I3(\result_o[23]_INST_0_i_3_n_0 ),
        .I4(\result_o[23]_INST_0_i_4_n_0 ),
        .I5(\result_o[23]_INST_0_i_5_n_0 ),
        .O(result_o[23]));
  (* SOFT_HLUTNM = "soft_lutpair45" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[23]_INST_0_i_1 
       (.I0(\result_o[24]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[23]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[23]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair48" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[23]_INST_0_i_10 
       (.I0(a_i[23]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[23]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[23]_INST_0_i_11 
       (.I0(a_i[29]),
        .I1(a_i[27]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[23]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair48" *) 
  LUT4 #(
    .INIT(16'h0B08)) 
    \result_o[23]_INST_0_i_12 
       (.I0(a_i[31]),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[23]),
        .O(\result_o[23]_INST_0_i_12_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair20" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[23]_INST_0_i_13 
       (.I0(a_i[16]),
        .I1(a_i[8]),
        .I2(a_i[0]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[23]_INST_0_i_13_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[23]_INST_0_i_14 
       (.I0(a_i[23]),
        .I1(b_i[23]),
        .O(\result_o[23]_INST_0_i_14_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[23]_INST_0_i_15 
       (.I0(a_i[22]),
        .I1(b_i[22]),
        .O(\result_o[23]_INST_0_i_15_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[23]_INST_0_i_16 
       (.I0(a_i[21]),
        .I1(b_i[21]),
        .O(\result_o[23]_INST_0_i_16_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[23]_INST_0_i_17 
       (.I0(a_i[20]),
        .I1(b_i[20]),
        .O(\result_o[23]_INST_0_i_17_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[23]_INST_0_i_2 
       (.I0(\result_o[24]_INST_0_i_7_n_0 ),
        .I1(\result_o[23]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[23]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[23]_INST_0_i_3 
       (.I0(\result_o[23]_INST_0_i_8_n_0 ),
        .I1(\result_o[24]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[23]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[23]_INST_0_i_4 
       (.I0(data0[23]),
        .I1(b_i[23]),
        .I2(a_i[23]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[23]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[23]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[23]),
        .O(\result_o[23]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[23]_INST_0_i_6 
       (.I0(\result_o[25]_INST_0_i_10_n_0 ),
        .I1(\result_o[29]_INST_0_i_7_n_0 ),
        .I2(\result_o[23]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[25]_INST_0_i_9_n_0 ),
        .O(\result_o[23]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hAAAEAFAEAAAEAAAE)) 
    \result_o[23]_INST_0_i_7 
       (.I0(\result_o[23]_INST_0_i_11_n_0 ),
        .I1(\result_o[23]_INST_0_i_12_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[30]_INST_0_i_9_n_0 ),
        .I5(a_i[25]),
        .O(\result_o[23]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[23]_INST_0_i_8 
       (.I0(\result_o[25]_INST_0_i_12_n_0 ),
        .I1(\result_o[23]_INST_0_i_13_n_0 ),
        .I2(\result_o[27]_INST_0_i_16_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[27]_INST_0_i_17_n_0 ),
        .O(\result_o[23]_INST_0_i_8_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[23]_INST_0_i_9 
       (.CI(\result_o[19]_INST_0_i_9_n_0 ),
        .CO({\result_o[23]_INST_0_i_9_n_0 ,\result_o[23]_INST_0_i_9_n_1 ,\result_o[23]_INST_0_i_9_n_2 ,\result_o[23]_INST_0_i_9_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[23:20]),
        .O(data0[23:20]),
        .S({\result_o[23]_INST_0_i_14_n_0 ,\result_o[23]_INST_0_i_15_n_0 ,\result_o[23]_INST_0_i_16_n_0 ,\result_o[23]_INST_0_i_17_n_0 }));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[24]_INST_0 
       (.I0(\result_o[24]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[24]_INST_0_i_2_n_0 ),
        .I3(\result_o[24]_INST_0_i_3_n_0 ),
        .I4(\result_o[24]_INST_0_i_4_n_0 ),
        .I5(\result_o[24]_INST_0_i_5_n_0 ),
        .O(result_o[24]));
  (* SOFT_HLUTNM = "soft_lutpair46" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[24]_INST_0_i_1 
       (.I0(\result_o[25]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[24]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[24]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[24]_INST_0_i_10 
       (.I0(a_i[26]),
        .I1(a_i[24]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[24]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair22" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[24]_INST_0_i_11 
       (.I0(a_i[17]),
        .I1(a_i[9]),
        .I2(a_i[1]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[24]_INST_0_i_11_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[24]_INST_0_i_2 
       (.I0(\result_o[25]_INST_0_i_7_n_0 ),
        .I1(\result_o[24]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[24]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[24]_INST_0_i_3 
       (.I0(\result_o[24]_INST_0_i_8_n_0 ),
        .I1(\result_o[25]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[24]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[24]_INST_0_i_4 
       (.I0(data0[24]),
        .I1(b_i[24]),
        .I2(a_i[24]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[24]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[24]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[24]),
        .O(\result_o[24]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[24]_INST_0_i_6 
       (.I0(\result_o[26]_INST_0_i_11_n_0 ),
        .I1(\result_o[29]_INST_0_i_6_n_0 ),
        .I2(\result_o[24]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[26]_INST_0_i_10_n_0 ),
        .O(\result_o[24]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFF44400400)) 
    \result_o[24]_INST_0_i_7 
       (.I0(\result_o[30]_INST_0_i_9_n_0 ),
        .I1(b_i[2]),
        .I2(b_i[1]),
        .I3(a_i[28]),
        .I4(a_i[30]),
        .I5(\result_o[24]_INST_0_i_10_n_0 ),
        .O(\result_o[24]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[24]_INST_0_i_8 
       (.I0(\result_o[26]_INST_0_i_12_n_0 ),
        .I1(\result_o[24]_INST_0_i_11_n_0 ),
        .I2(\result_o[28]_INST_0_i_14_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[28]_INST_0_i_15_n_0 ),
        .O(\result_o[24]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair19" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[24]_INST_0_i_9 
       (.I0(a_i[24]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[24]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[25]_INST_0 
       (.I0(\result_o[25]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[25]_INST_0_i_2_n_0 ),
        .I3(\result_o[25]_INST_0_i_3_n_0 ),
        .I4(\result_o[25]_INST_0_i_4_n_0 ),
        .I5(\result_o[25]_INST_0_i_5_n_0 ),
        .O(result_o[25]));
  (* SOFT_HLUTNM = "soft_lutpair46" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[25]_INST_0_i_1 
       (.I0(\result_o[26]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[25]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[25]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair25" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[25]_INST_0_i_10 
       (.I0(a_i[27]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[25]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[25]_INST_0_i_11 
       (.I0(a_i[27]),
        .I1(a_i[25]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[25]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair24" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[25]_INST_0_i_12 
       (.I0(a_i[18]),
        .I1(a_i[10]),
        .I2(a_i[2]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[25]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[25]_INST_0_i_2 
       (.I0(\result_o[26]_INST_0_i_8_n_0 ),
        .I1(\result_o[25]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[25]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[25]_INST_0_i_3 
       (.I0(\result_o[25]_INST_0_i_8_n_0 ),
        .I1(\result_o[26]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[25]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[25]_INST_0_i_4 
       (.I0(data0[25]),
        .I1(b_i[25]),
        .I2(a_i[25]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[25]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[25]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[25]),
        .O(\result_o[25]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[25]_INST_0_i_6 
       (.I0(\result_o[29]_INST_0_i_7_n_0 ),
        .I1(a_i[31]),
        .I2(\result_o[25]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[25]_INST_0_i_10_n_0 ),
        .O(\result_o[25]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFF44400400)) 
    \result_o[25]_INST_0_i_7 
       (.I0(\result_o[30]_INST_0_i_9_n_0 ),
        .I1(b_i[2]),
        .I2(b_i[1]),
        .I3(a_i[29]),
        .I4(a_i[31]),
        .I5(\result_o[25]_INST_0_i_11_n_0 ),
        .O(\result_o[25]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[25]_INST_0_i_8 
       (.I0(\result_o[27]_INST_0_i_17_n_0 ),
        .I1(\result_o[25]_INST_0_i_12_n_0 ),
        .I2(\result_o[31]_INST_0_i_20_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[27]_INST_0_i_16_n_0 ),
        .O(\result_o[25]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair21" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[25]_INST_0_i_9 
       (.I0(a_i[25]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[25]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[26]_INST_0 
       (.I0(\result_o[26]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[26]_INST_0_i_2_n_0 ),
        .I3(\result_o[26]_INST_0_i_3_n_0 ),
        .I4(\result_o[26]_INST_0_i_4_n_0 ),
        .I5(\result_o[26]_INST_0_i_5_n_0 ),
        .O(result_o[26]));
  (* SOFT_HLUTNM = "soft_lutpair47" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[26]_INST_0_i_1 
       (.I0(\result_o[27]_INST_0_i_5_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[26]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[26]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair23" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[26]_INST_0_i_10 
       (.I0(a_i[26]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[26]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair27" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[26]_INST_0_i_11 
       (.I0(a_i[28]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[26]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair26" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[26]_INST_0_i_12 
       (.I0(a_i[19]),
        .I1(a_i[11]),
        .I2(a_i[3]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[26]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[26]_INST_0_i_2 
       (.I0(\result_o[26]_INST_0_i_7_n_0 ),
        .I1(\result_o[26]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[26]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[26]_INST_0_i_3 
       (.I0(\result_o[26]_INST_0_i_9_n_0 ),
        .I1(\result_o[27]_INST_0_i_7_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[26]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[26]_INST_0_i_4 
       (.I0(data0[26]),
        .I1(b_i[26]),
        .I2(a_i[26]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[26]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[26]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[26]),
        .O(\result_o[26]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[26]_INST_0_i_6 
       (.I0(\result_o[29]_INST_0_i_6_n_0 ),
        .I1(a_i[31]),
        .I2(\result_o[26]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[26]_INST_0_i_11_n_0 ),
        .O(\result_o[26]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000F0CCAA)) 
    \result_o[26]_INST_0_i_7 
       (.I0(a_i[27]),
        .I1(a_i[29]),
        .I2(a_i[31]),
        .I3(b_i[1]),
        .I4(b_i[2]),
        .I5(\result_o[30]_INST_0_i_9_n_0 ),
        .O(\result_o[26]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000F0CCAA)) 
    \result_o[26]_INST_0_i_8 
       (.I0(a_i[26]),
        .I1(a_i[28]),
        .I2(a_i[30]),
        .I3(b_i[1]),
        .I4(b_i[2]),
        .I5(\result_o[30]_INST_0_i_9_n_0 ),
        .O(\result_o[26]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[26]_INST_0_i_9 
       (.I0(\result_o[28]_INST_0_i_15_n_0 ),
        .I1(\result_o[26]_INST_0_i_12_n_0 ),
        .I2(\result_o[31]_INST_0_i_26_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[28]_INST_0_i_14_n_0 ),
        .O(\result_o[26]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFEEEAEEEAEEEA)) 
    \result_o[27]_INST_0 
       (.I0(\result_o[27]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[27]_INST_0_i_2_n_0 ),
        .I3(\result_o[27]_INST_0_i_3_n_0 ),
        .I4(\result_o[28]_INST_0_i_4_n_0 ),
        .I5(data1[27]),
        .O(result_o[27]));
  (* SOFT_HLUTNM = "soft_lutpair47" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[27]_INST_0_i_1 
       (.I0(\result_o[28]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[27]_INST_0_i_5_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[27]_INST_0_i_1_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_10 
       (.I0(b_i[27]),
        .I1(a_i[27]),
        .O(\result_o[27]_INST_0_i_10_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_11 
       (.I0(b_i[26]),
        .I1(a_i[26]),
        .O(\result_o[27]_INST_0_i_11_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_12 
       (.I0(b_i[25]),
        .I1(a_i[25]),
        .O(\result_o[27]_INST_0_i_12_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_13 
       (.I0(b_i[24]),
        .I1(a_i[24]),
        .O(\result_o[27]_INST_0_i_13_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[27]_INST_0_i_14 
       (.I0(a_i[29]),
        .I1(a_i[27]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[27]_INST_0_i_14_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair7" *) 
  LUT4 #(
    .INIT(16'h0004)) 
    \result_o[27]_INST_0_i_15 
       (.I0(b_i[1]),
        .I1(b_i[2]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .O(\result_o[27]_INST_0_i_15_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair32" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[27]_INST_0_i_16 
       (.I0(a_i[22]),
        .I1(a_i[14]),
        .I2(a_i[6]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[27]_INST_0_i_16_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair28" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[27]_INST_0_i_17 
       (.I0(a_i[20]),
        .I1(a_i[12]),
        .I2(a_i[4]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[27]_INST_0_i_17_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[27]_INST_0_i_18 
       (.I0(a_i[27]),
        .I1(b_i[27]),
        .O(\result_o[27]_INST_0_i_18_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[27]_INST_0_i_19 
       (.I0(a_i[26]),
        .I1(b_i[26]),
        .O(\result_o[27]_INST_0_i_19_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[27]_INST_0_i_2 
       (.I0(\result_o[27]_INST_0_i_6_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[28]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[27]_INST_0_i_7_n_0 ),
        .O(\result_o[27]_INST_0_i_2_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[27]_INST_0_i_20 
       (.I0(a_i[25]),
        .I1(b_i[25]),
        .O(\result_o[27]_INST_0_i_20_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[27]_INST_0_i_21 
       (.I0(a_i[24]),
        .I1(b_i[24]),
        .O(\result_o[27]_INST_0_i_21_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_22 
       (.I0(b_i[23]),
        .I1(a_i[23]),
        .O(\result_o[27]_INST_0_i_22_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_23 
       (.I0(b_i[22]),
        .I1(a_i[22]),
        .O(\result_o[27]_INST_0_i_23_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_24 
       (.I0(b_i[21]),
        .I1(a_i[21]),
        .O(\result_o[27]_INST_0_i_24_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[27]_INST_0_i_25 
       (.I0(b_i[20]),
        .I1(a_i[20]),
        .O(\result_o[27]_INST_0_i_25_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[27]_INST_0_i_3 
       (.I0(data0[27]),
        .I1(b_i[27]),
        .I2(a_i[27]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[27]_INST_0_i_3_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[27]_INST_0_i_4 
       (.CI(\result_o[27]_INST_0_i_9_n_0 ),
        .CO({\result_o[27]_INST_0_i_4_n_0 ,\result_o[27]_INST_0_i_4_n_1 ,\result_o[27]_INST_0_i_4_n_2 ,\result_o[27]_INST_0_i_4_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[27:24]),
        .O(data1[27:24]),
        .S({\result_o[27]_INST_0_i_10_n_0 ,\result_o[27]_INST_0_i_11_n_0 ,\result_o[27]_INST_0_i_12_n_0 ,\result_o[27]_INST_0_i_13_n_0 }));
  LUT6 #(
    .INIT(64'hFFFF0000FEAE5404)) 
    \result_o[27]_INST_0_i_5 
       (.I0(\result_o[30]_INST_0_i_9_n_0 ),
        .I1(a_i[27]),
        .I2(b_i[1]),
        .I3(a_i[29]),
        .I4(a_i[31]),
        .I5(b_i[2]),
        .O(\result_o[27]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hFFF8F8F888888888)) 
    \result_o[27]_INST_0_i_6 
       (.I0(\result_o[28]_INST_0_i_13_n_0 ),
        .I1(\result_o[30]_INST_0_i_11_n_0 ),
        .I2(\result_o[27]_INST_0_i_14_n_0 ),
        .I3(a_i[31]),
        .I4(\result_o[27]_INST_0_i_15_n_0 ),
        .I5(\result_o[30]_INST_0_i_12_n_0 ),
        .O(\result_o[27]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[27]_INST_0_i_7 
       (.I0(\result_o[27]_INST_0_i_16_n_0 ),
        .I1(\result_o[27]_INST_0_i_17_n_0 ),
        .I2(\result_o[31]_INST_0_i_9_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[31]_INST_0_i_20_n_0 ),
        .O(\result_o[27]_INST_0_i_7_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[27]_INST_0_i_8 
       (.CI(\result_o[23]_INST_0_i_9_n_0 ),
        .CO({\result_o[27]_INST_0_i_8_n_0 ,\result_o[27]_INST_0_i_8_n_1 ,\result_o[27]_INST_0_i_8_n_2 ,\result_o[27]_INST_0_i_8_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[27:24]),
        .O(data0[27:24]),
        .S({\result_o[27]_INST_0_i_18_n_0 ,\result_o[27]_INST_0_i_19_n_0 ,\result_o[27]_INST_0_i_20_n_0 ,\result_o[27]_INST_0_i_21_n_0 }));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[27]_INST_0_i_9 
       (.CI(\result_o[19]_INST_0_i_10_n_0 ),
        .CO({\result_o[27]_INST_0_i_9_n_0 ,\result_o[27]_INST_0_i_9_n_1 ,\result_o[27]_INST_0_i_9_n_2 ,\result_o[27]_INST_0_i_9_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[23:20]),
        .O(data1[23:20]),
        .S({\result_o[27]_INST_0_i_22_n_0 ,\result_o[27]_INST_0_i_23_n_0 ,\result_o[27]_INST_0_i_24_n_0 ,\result_o[27]_INST_0_i_25_n_0 }));
  LUT6 #(
    .INIT(64'hFFFFEEEAEEEAEEEA)) 
    \result_o[28]_INST_0 
       (.I0(\result_o[28]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[28]_INST_0_i_2_n_0 ),
        .I3(\result_o[28]_INST_0_i_3_n_0 ),
        .I4(\result_o[28]_INST_0_i_4_n_0 ),
        .I5(data1[28]),
        .O(result_o[28]));
  LUT6 #(
    .INIT(64'hFFFFB800B800B800)) 
    \result_o[28]_INST_0_i_1 
       (.I0(a_i[31]),
        .I1(\result_o[30]_INST_0_i_8_n_0 ),
        .I2(\result_o[29]_INST_0_i_7_n_0 ),
        .I3(\result_o[30]_INST_0_i_7_n_0 ),
        .I4(\result_o[28]_INST_0_i_6_n_0 ),
        .I5(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[28]_INST_0_i_1_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[28]_INST_0_i_10 
       (.I0(b_i[30]),
        .I1(a_i[30]),
        .O(\result_o[28]_INST_0_i_10_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[28]_INST_0_i_11 
       (.I0(b_i[29]),
        .I1(a_i[29]),
        .O(\result_o[28]_INST_0_i_11_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[28]_INST_0_i_12 
       (.I0(b_i[28]),
        .I1(a_i[28]),
        .O(\result_o[28]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[28]_INST_0_i_13 
       (.I0(a_i[30]),
        .I1(a_i[28]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[28]_INST_0_i_13_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair33" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[28]_INST_0_i_14 
       (.I0(a_i[23]),
        .I1(a_i[15]),
        .I2(a_i[7]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[28]_INST_0_i_14_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair30" *) 
  LUT5 #(
    .INIT(32'h00CCF0AA)) 
    \result_o[28]_INST_0_i_15 
       (.I0(a_i[21]),
        .I1(a_i[13]),
        .I2(a_i[5]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .O(\result_o[28]_INST_0_i_15_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFEEEAEEEAEEEA)) 
    \result_o[28]_INST_0_i_2 
       (.I0(\result_o[28]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[29]_INST_0_i_10_n_0 ),
        .I3(\result_o[29]_INST_0_i_9_n_0 ),
        .I4(\result_o[30]_INST_0_i_15_n_0 ),
        .I5(\result_o[28]_INST_0_i_8_n_0 ),
        .O(\result_o[28]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[28]_INST_0_i_3 
       (.I0(data0[28]),
        .I1(b_i[28]),
        .I2(a_i[28]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[28]_INST_0_i_3_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT5 #(
    .INIT(32'h00010000)) 
    \result_o[28]_INST_0_i_4 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[4]),
        .I4(alu_op_i[3]),
        .O(\result_o[28]_INST_0_i_4_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[28]_INST_0_i_5 
       (.CI(\result_o[27]_INST_0_i_4_n_0 ),
        .CO({\result_o[28]_INST_0_i_5_n_1 ,\result_o[28]_INST_0_i_5_n_2 ,\result_o[28]_INST_0_i_5_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\<const0> ,a_i[30:28]}),
        .O(data1[31:28]),
        .S({\result_o[28]_INST_0_i_9_n_0 ,\result_o[28]_INST_0_i_10_n_0 ,\result_o[28]_INST_0_i_11_n_0 ,\result_o[28]_INST_0_i_12_n_0 }));
  LUT6 #(
    .INIT(64'hFFFF0000FEAE5404)) 
    \result_o[28]_INST_0_i_6 
       (.I0(\result_o[30]_INST_0_i_9_n_0 ),
        .I1(a_i[28]),
        .I2(b_i[1]),
        .I3(a_i[30]),
        .I4(a_i[31]),
        .I5(b_i[2]),
        .O(\result_o[28]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[28]_INST_0_i_7 
       (.I0(\result_o[29]_INST_0_i_8_n_0 ),
        .I1(\result_o[28]_INST_0_i_13_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[28]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[28]_INST_0_i_8 
       (.I0(\result_o[28]_INST_0_i_14_n_0 ),
        .I1(\result_o[28]_INST_0_i_15_n_0 ),
        .I2(\result_o[31]_INST_0_i_24_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[31]_INST_0_i_26_n_0 ),
        .O(\result_o[28]_INST_0_i_8_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[28]_INST_0_i_9 
       (.I0(b_i[31]),
        .I1(a_i[31]),
        .O(\result_o[28]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[29]_INST_0 
       (.I0(\result_o[29]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[29]_INST_0_i_2_n_0 ),
        .I3(\result_o[29]_INST_0_i_3_n_0 ),
        .I4(\result_o[29]_INST_0_i_4_n_0 ),
        .I5(\result_o[29]_INST_0_i_5_n_0 ),
        .O(result_o[29]));
  LUT6 #(
    .INIT(64'hF0FFF088C088C088)) 
    \result_o[29]_INST_0_i_1 
       (.I0(\result_o[29]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(a_i[31]),
        .I3(\result_o[30]_INST_0_i_8_n_0 ),
        .I4(\result_o[29]_INST_0_i_7_n_0 ),
        .I5(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[29]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h2A0A220228082000)) 
    \result_o[29]_INST_0_i_10 
       (.I0(\result_o[3]_INST_0_i_7_n_0 ),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[6]),
        .I4(a_i[14]),
        .I5(a_i[22]),
        .O(\result_o[29]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'hFFFF020002000200)) 
    \result_o[29]_INST_0_i_2 
       (.I0(\result_o[30]_INST_0_i_11_n_0 ),
        .I1(\result_o[30]_INST_0_i_9_n_0 ),
        .I2(\result_o[30]_INST_0_i_8_n_0 ),
        .I3(a_i[30]),
        .I4(\result_o[29]_INST_0_i_8_n_0 ),
        .I5(\result_o[30]_INST_0_i_12_n_0 ),
        .O(\result_o[29]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFE0E0E0E0E0)) 
    \result_o[29]_INST_0_i_3 
       (.I0(\result_o[29]_INST_0_i_9_n_0 ),
        .I1(\result_o[29]_INST_0_i_10_n_0 ),
        .I2(\result_o[30]_INST_0_i_15_n_0 ),
        .I3(\result_o[30]_INST_0_i_13_n_0 ),
        .I4(\result_o[30]_INST_0_i_14_n_0 ),
        .I5(\result_o[31]_INST_0_i_11_n_0 ),
        .O(\result_o[29]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[29]_INST_0_i_4 
       (.I0(data0[29]),
        .I1(b_i[29]),
        .I2(a_i[29]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[29]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[29]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[29]),
        .O(\result_o[29]_INST_0_i_5_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair31" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[29]_INST_0_i_6 
       (.I0(a_i[30]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[29]_INST_0_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair29" *) 
  LUT4 #(
    .INIT(16'hCCCA)) 
    \result_o[29]_INST_0_i_7 
       (.I0(a_i[29]),
        .I1(a_i[31]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .O(\result_o[29]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[29]_INST_0_i_8 
       (.I0(a_i[31]),
        .I1(a_i[29]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[29]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'h33BB33BB33BB3088)) 
    \result_o[29]_INST_0_i_9 
       (.I0(\result_o[31]_INST_0_i_9_n_0 ),
        .I1(b_i[1]),
        .I2(\result_o[31]_INST_0_i_20_n_0 ),
        .I3(b_i[2]),
        .I4(\result_o[31]_INST_0_i_21_n_0 ),
        .I5(\result_o[31]_INST_0_i_22_n_0 ),
        .O(\result_o[29]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[2]_INST_0 
       (.I0(\result_o[2]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[2]_INST_0_i_2_n_0 ),
        .I3(\result_o[2]_INST_0_i_3_n_0 ),
        .I4(\result_o[2]_INST_0_i_4_n_0 ),
        .I5(\result_o[2]_INST_0_i_5_n_0 ),
        .O(result_o[2]));
  LUT6 #(
    .INIT(64'hFFFFFFE0E0E0E0E0)) 
    \result_o[2]_INST_0_i_1 
       (.I0(\result_o[2]_INST_0_i_6_n_0 ),
        .I1(\result_o[3]_INST_0_i_8_n_0 ),
        .I2(\result_o[30]_INST_0_i_7_n_0 ),
        .I3(\result_o[2]_INST_0_i_7_n_0 ),
        .I4(\result_o[2]_INST_0_i_8_n_0 ),
        .I5(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[2]_INST_0_i_1_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT5 #(
    .INIT(32'h00010000)) 
    \result_o[2]_INST_0_i_10 
       (.I0(b_i[3]),
        .I1(b_i[4]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[1]),
        .O(\result_o[2]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h0088A0AA0088A000)) 
    \result_o[2]_INST_0_i_11 
       (.I0(\result_o[3]_INST_0_i_7_n_0 ),
        .I1(a_i[25]),
        .I2(a_i[17]),
        .I3(b_i[3]),
        .I4(b_i[4]),
        .I5(a_i[9]),
        .O(\result_o[2]_INST_0_i_11_n_0 ));
  LUT6 #(
    .INIT(64'h0088A0AA0088A000)) 
    \result_o[2]_INST_0_i_12 
       (.I0(\result_o[3]_INST_0_i_7_n_0 ),
        .I1(a_i[24]),
        .I2(a_i[16]),
        .I3(b_i[3]),
        .I4(b_i[4]),
        .I5(a_i[8]),
        .O(\result_o[2]_INST_0_i_12_n_0 ));
  LUT5 #(
    .INIT(32'h00000A0C)) 
    \result_o[2]_INST_0_i_13 
       (.I0(a_i[10]),
        .I1(a_i[2]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(b_i[2]),
        .O(\result_o[2]_INST_0_i_13_n_0 ));
  LUT5 #(
    .INIT(32'h0000AC00)) 
    \result_o[2]_INST_0_i_14 
       (.I0(a_i[26]),
        .I1(a_i[18]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .O(\result_o[2]_INST_0_i_14_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFA8FFA8FFA8)) 
    \result_o[2]_INST_0_i_2 
       (.I0(\result_o[31]_INST_0_i_16_n_0 ),
        .I1(a_i[2]),
        .I2(b_i[2]),
        .I3(\result_o[2]_INST_0_i_9_n_0 ),
        .I4(\result_o[2]_INST_0_i_10_n_0 ),
        .I5(\result_o[30]_INST_0_i_15_n_0 ),
        .O(\result_o[2]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hC1C0454445440100)) 
    \result_o[2]_INST_0_i_3 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(data0[2]),
        .I4(a_i[2]),
        .I5(b_i[2]),
        .O(\result_o[2]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFE0E0E0E0E0)) 
    \result_o[2]_INST_0_i_4 
       (.I0(\result_o[2]_INST_0_i_11_n_0 ),
        .I1(\result_o[3]_INST_0_i_8_n_0 ),
        .I2(\result_o[30]_INST_0_i_11_n_0 ),
        .I3(\result_o[2]_INST_0_i_12_n_0 ),
        .I4(\result_o[2]_INST_0_i_8_n_0 ),
        .I5(\result_o[30]_INST_0_i_12_n_0 ),
        .O(\result_o[2]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[2]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[2]),
        .O(\result_o[2]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'h8888888880000000)) 
    \result_o[2]_INST_0_i_6 
       (.I0(b_i[2]),
        .I1(b_i[1]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(a_i[31]),
        .I5(\result_o[3]_INST_0_i_11_n_0 ),
        .O(\result_o[2]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'h8888888880000000)) 
    \result_o[2]_INST_0_i_7 
       (.I0(b_i[2]),
        .I1(b_i[1]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(a_i[31]),
        .I5(\result_o[8]_INST_0_i_12_n_0 ),
        .O(\result_o[2]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h33BB33BB33BB3088)) 
    \result_o[2]_INST_0_i_8 
       (.I0(\result_o[4]_INST_0_i_10_n_0 ),
        .I1(b_i[1]),
        .I2(\result_o[6]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(\result_o[2]_INST_0_i_13_n_0 ),
        .I5(\result_o[2]_INST_0_i_14_n_0 ),
        .O(\result_o[2]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'h0022002000020000)) 
    \result_o[2]_INST_0_i_9 
       (.I0(\result_o[31]_INST_0_i_11_n_0 ),
        .I1(\result_o[30]_INST_0_i_9_n_0 ),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(a_i[2]),
        .I5(a_i[0]),
        .O(\result_o[2]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[30]_INST_0 
       (.I0(\result_o[30]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[30]_INST_0_i_3_n_0 ),
        .I3(\result_o[30]_INST_0_i_4_n_0 ),
        .I4(\result_o[30]_INST_0_i_5_n_0 ),
        .I5(\result_o[30]_INST_0_i_6_n_0 ),
        .O(result_o[30]));
  LUT6 #(
    .INIT(64'hFF00FE30AA00AA00)) 
    \result_o[30]_INST_0_i_1 
       (.I0(\result_o[30]_INST_0_i_7_n_0 ),
        .I1(\result_o[30]_INST_0_i_8_n_0 ),
        .I2(a_i[30]),
        .I3(a_i[31]),
        .I4(\result_o[30]_INST_0_i_9_n_0 ),
        .I5(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[30]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000004000)) 
    \result_o[30]_INST_0_i_10 
       (.I0(alu_op_i[1]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[3]),
        .I4(alu_op_i[4]),
        .I5(b_i[0]),
        .O(\result_o[30]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair35" *) 
  LUT4 #(
    .INIT(16'h0800)) 
    \result_o[30]_INST_0_i_11 
       (.I0(alu_op_i[2]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[1]),
        .I3(b_i[0]),
        .O(\result_o[30]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair35" *) 
  LUT4 #(
    .INIT(16'h0008)) 
    \result_o[30]_INST_0_i_12 
       (.I0(alu_op_i[2]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[1]),
        .I3(b_i[0]),
        .O(\result_o[30]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h33BB33BB33BB3088)) 
    \result_o[30]_INST_0_i_13 
       (.I0(\result_o[31]_INST_0_i_24_n_0 ),
        .I1(b_i[1]),
        .I2(\result_o[31]_INST_0_i_26_n_0 ),
        .I3(b_i[2]),
        .I4(\result_o[31]_INST_0_i_27_n_0 ),
        .I5(\result_o[31]_INST_0_i_28_n_0 ),
        .O(\result_o[30]_INST_0_i_13_n_0 ));
  LUT6 #(
    .INIT(64'h2A0A220228082000)) 
    \result_o[30]_INST_0_i_14 
       (.I0(\result_o[3]_INST_0_i_7_n_0 ),
        .I1(b_i[3]),
        .I2(b_i[4]),
        .I3(a_i[7]),
        .I4(a_i[15]),
        .I5(a_i[23]),
        .O(\result_o[30]_INST_0_i_14_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair34" *) 
  LUT4 #(
    .INIT(16'h0400)) 
    \result_o[30]_INST_0_i_15 
       (.I0(alu_op_i[2]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[1]),
        .I3(b_i[0]),
        .O(\result_o[30]_INST_0_i_15_n_0 ));
  LUT6 #(
    .INIT(64'hEEEEEEEEEEEEEAAA)) 
    \result_o[30]_INST_0_i_16 
       (.I0(\result_o[31]_INST_0_i_8_n_0 ),
        .I1(b_i[1]),
        .I2(\result_o[31]_INST_0_i_20_n_0 ),
        .I3(b_i[2]),
        .I4(\result_o[31]_INST_0_i_21_n_0 ),
        .I5(\result_o[31]_INST_0_i_22_n_0 ),
        .O(\result_o[30]_INST_0_i_16_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFF888F888F888)) 
    \result_o[30]_INST_0_i_17 
       (.I0(\result_o[0]_INST_0_i_8_n_0 ),
        .I1(a_i[30]),
        .I2(\result_o[31]_INST_0_i_23_n_0 ),
        .I3(a_i[22]),
        .I4(\result_o[31]_INST_0_i_9_n_0 ),
        .I5(\result_o[31]_INST_0_i_25_n_0 ),
        .O(\result_o[30]_INST_0_i_17_n_0 ));
  LUT2 #(
    .INIT(4'h1)) 
    \result_o[30]_INST_0_i_2 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .O(\result_o[30]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h000000F800000088)) 
    \result_o[30]_INST_0_i_3 
       (.I0(\result_o[30]_INST_0_i_11_n_0 ),
        .I1(a_i[31]),
        .I2(\result_o[30]_INST_0_i_12_n_0 ),
        .I3(\result_o[30]_INST_0_i_9_n_0 ),
        .I4(\result_o[30]_INST_0_i_8_n_0 ),
        .I5(a_i[30]),
        .O(\result_o[30]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFE0E0E0E0E0)) 
    \result_o[30]_INST_0_i_4 
       (.I0(\result_o[30]_INST_0_i_13_n_0 ),
        .I1(\result_o[30]_INST_0_i_14_n_0 ),
        .I2(\result_o[30]_INST_0_i_15_n_0 ),
        .I3(\result_o[30]_INST_0_i_16_n_0 ),
        .I4(\result_o[30]_INST_0_i_17_n_0 ),
        .I5(\result_o[31]_INST_0_i_11_n_0 ),
        .O(\result_o[30]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'hC0000000FC3C00AA)) 
    \result_o[30]_INST_0_i_5 
       (.I0(data0[30]),
        .I1(b_i[30]),
        .I2(a_i[30]),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[0]),
        .O(\result_o[30]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[30]_INST_0_i_6 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[30]),
        .O(\result_o[30]_INST_0_i_6_n_0 ));
  LUT6 #(
    .INIT(64'h0000400000000000)) 
    \result_o[30]_INST_0_i_7 
       (.I0(alu_op_i[1]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[3]),
        .I4(alu_op_i[4]),
        .I5(b_i[0]),
        .O(\result_o[30]_INST_0_i_7_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair2" *) 
  LUT2 #(
    .INIT(4'hE)) 
    \result_o[30]_INST_0_i_8 
       (.I0(b_i[1]),
        .I1(b_i[2]),
        .O(\result_o[30]_INST_0_i_8_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair8" *) 
  LUT2 #(
    .INIT(4'hE)) 
    \result_o[30]_INST_0_i_9 
       (.I0(b_i[3]),
        .I1(b_i[4]),
        .O(\result_o[30]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFFFFFFFF8)) 
    \result_o[31]_INST_0 
       (.I0(\result_o[31]_INST_0_i_1_n_0 ),
        .I1(\result_o[31]_INST_0_i_2_n_0 ),
        .I2(\result_o[31]_INST_0_i_3_n_0 ),
        .I3(\result_o[31]_INST_0_i_4_n_0 ),
        .I4(\result_o[31]_INST_0_i_5_n_0 ),
        .I5(\result_o[31]_INST_0_i_6_n_0 ),
        .O(result_o[31]));
  LUT6 #(
    .INIT(64'hFFFFFFFFEFECECEC)) 
    \result_o[31]_INST_0_i_1 
       (.I0(\result_o[31]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_8_n_0 ),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(\result_o[31]_INST_0_i_9_n_0 ),
        .I5(\result_o[31]_INST_0_i_10_n_0 ),
        .O(\result_o[31]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h0000000A0000000C)) 
    \result_o[31]_INST_0_i_10 
       (.I0(a_i[22]),
        .I1(a_i[30]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[31]_INST_0_i_10_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair34" *) 
  LUT4 #(
    .INIT(16'h0004)) 
    \result_o[31]_INST_0_i_11 
       (.I0(alu_op_i[2]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[1]),
        .I3(b_i[0]),
        .O(\result_o[31]_INST_0_i_11_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFF888F888F888)) 
    \result_o[31]_INST_0_i_12 
       (.I0(\result_o[0]_INST_0_i_8_n_0 ),
        .I1(a_i[31]),
        .I2(\result_o[31]_INST_0_i_23_n_0 ),
        .I3(a_i[23]),
        .I4(\result_o[31]_INST_0_i_24_n_0 ),
        .I5(\result_o[31]_INST_0_i_25_n_0 ),
        .O(\result_o[31]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[31]_INST_0_i_13 
       (.I0(a_i[7]),
        .I1(a_i[15]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .I5(b_i[1]),
        .O(\result_o[31]_INST_0_i_13_n_0 ));
  LUT4 #(
    .INIT(16'hFFF8)) 
    \result_o[31]_INST_0_i_14 
       (.I0(\result_o[31]_INST_0_i_26_n_0 ),
        .I1(b_i[2]),
        .I2(\result_o[31]_INST_0_i_27_n_0 ),
        .I3(\result_o[31]_INST_0_i_28_n_0 ),
        .O(\result_o[31]_INST_0_i_14_n_0 ));
  LUT6 #(
    .INIT(64'h010000FF01FF0000)) 
    \result_o[31]_INST_0_i_15 
       (.I0(\result_o[30]_INST_0_i_8_n_0 ),
        .I1(\result_o[30]_INST_0_i_9_n_0 ),
        .I2(b_i[0]),
        .I3(alu_op_i[0]),
        .I4(a_i[31]),
        .I5(b_i[31]),
        .O(\result_o[31]_INST_0_i_15_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair10" *) 
  LUT3 #(
    .INIT(8'h40)) 
    \result_o[31]_INST_0_i_16 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .O(\result_o[31]_INST_0_i_16_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT3 #(
    .INIT(8'h01)) 
    \result_o[31]_INST_0_i_17 
       (.I0(alu_op_i[1]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[0]),
        .O(\result_o[31]_INST_0_i_17_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[31]_INST_0_i_18 
       (.CI(\result_o[27]_INST_0_i_8_n_0 ),
        .CO({\result_o[31]_INST_0_i_18_n_1 ,\result_o[31]_INST_0_i_18_n_2 ,\result_o[31]_INST_0_i_18_n_3 }),
        .CYINIT(\<const0> ),
        .DI({\<const0> ,a_i[30:28]}),
        .O(data0[31:28]),
        .S({\result_o[31]_INST_0_i_29_n_0 ,\result_o[31]_INST_0_i_30_n_0 ,\result_o[31]_INST_0_i_31_n_0 ,\result_o[31]_INST_0_i_32_n_0 }));
  (* SOFT_HLUTNM = "soft_lutpair9" *) 
  LUT3 #(
    .INIT(8'h40)) 
    \result_o[31]_INST_0_i_19 
       (.I0(alu_op_i[1]),
        .I1(alu_op_i[0]),
        .I2(alu_op_i[2]),
        .O(\result_o[31]_INST_0_i_19_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000020)) 
    \result_o[31]_INST_0_i_2 
       (.I0(b_i[0]),
        .I1(alu_op_i[1]),
        .I2(alu_op_i[0]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[4]),
        .I5(alu_op_i[3]),
        .O(\result_o[31]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[31]_INST_0_i_20 
       (.I0(a_i[8]),
        .I1(a_i[0]),
        .I2(a_i[24]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[16]),
        .O(\result_o[31]_INST_0_i_20_n_0 ));
  LUT5 #(
    .INIT(32'h00000A0C)) 
    \result_o[31]_INST_0_i_21 
       (.I0(a_i[20]),
        .I1(a_i[28]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(b_i[2]),
        .O(\result_o[31]_INST_0_i_21_n_0 ));
  LUT5 #(
    .INIT(32'h0000AC00)) 
    \result_o[31]_INST_0_i_22 
       (.I0(a_i[4]),
        .I1(a_i[12]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .O(\result_o[31]_INST_0_i_22_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair5" *) 
  LUT4 #(
    .INIT(16'h0004)) 
    \result_o[31]_INST_0_i_23 
       (.I0(b_i[4]),
        .I1(b_i[3]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .O(\result_o[31]_INST_0_i_23_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[31]_INST_0_i_24 
       (.I0(a_i[11]),
        .I1(a_i[3]),
        .I2(a_i[27]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[19]),
        .O(\result_o[31]_INST_0_i_24_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair3" *) 
  LUT2 #(
    .INIT(4'h2)) 
    \result_o[31]_INST_0_i_25 
       (.I0(b_i[2]),
        .I1(b_i[1]),
        .O(\result_o[31]_INST_0_i_25_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[31]_INST_0_i_26 
       (.I0(a_i[9]),
        .I1(a_i[1]),
        .I2(a_i[25]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[17]),
        .O(\result_o[31]_INST_0_i_26_n_0 ));
  LUT5 #(
    .INIT(32'h00000A0C)) 
    \result_o[31]_INST_0_i_27 
       (.I0(a_i[21]),
        .I1(a_i[29]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(b_i[2]),
        .O(\result_o[31]_INST_0_i_27_n_0 ));
  LUT5 #(
    .INIT(32'h0000AC00)) 
    \result_o[31]_INST_0_i_28 
       (.I0(a_i[5]),
        .I1(a_i[13]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .O(\result_o[31]_INST_0_i_28_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[31]_INST_0_i_29 
       (.I0(a_i[31]),
        .I1(b_i[31]),
        .O(\result_o[31]_INST_0_i_29_n_0 ));
  LUT6 #(
    .INIT(64'h8888888088808880)) 
    \result_o[31]_INST_0_i_3 
       (.I0(\result_o[30]_INST_0_i_2_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[31]_INST_0_i_12_n_0 ),
        .I3(\result_o[31]_INST_0_i_13_n_0 ),
        .I4(b_i[1]),
        .I5(\result_o[31]_INST_0_i_14_n_0 ),
        .O(\result_o[31]_INST_0_i_3_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[31]_INST_0_i_30 
       (.I0(a_i[30]),
        .I1(b_i[30]),
        .O(\result_o[31]_INST_0_i_30_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[31]_INST_0_i_31 
       (.I0(a_i[29]),
        .I1(b_i[29]),
        .O(\result_o[31]_INST_0_i_31_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[31]_INST_0_i_32 
       (.I0(a_i[28]),
        .I1(b_i[28]),
        .O(\result_o[31]_INST_0_i_32_n_0 ));
  LUT6 #(
    .INIT(64'h88F0000000000000)) 
    \result_o[31]_INST_0_i_4 
       (.I0(b_i[31]),
        .I1(a_i[31]),
        .I2(\result_o[31]_INST_0_i_15_n_0 ),
        .I3(alu_op_i[1]),
        .I4(alu_op_i[2]),
        .I5(\result_o[30]_INST_0_i_2_n_0 ),
        .O(\result_o[31]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'hFFA80000A8A80000)) 
    \result_o[31]_INST_0_i_5 
       (.I0(\result_o[31]_INST_0_i_16_n_0 ),
        .I1(b_i[31]),
        .I2(a_i[31]),
        .I3(\result_o[31]_INST_0_i_17_n_0 ),
        .I4(\result_o[30]_INST_0_i_2_n_0 ),
        .I5(data0[31]),
        .O(\result_o[31]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'h0000F88800000000)) 
    \result_o[31]_INST_0_i_6 
       (.I0(a_i[31]),
        .I1(\result_o[31]_INST_0_i_19_n_0 ),
        .I2(data1[31]),
        .I3(\result_o[31]_INST_0_i_17_n_0 ),
        .I4(alu_op_i[4]),
        .I5(alu_op_i[3]),
        .O(\result_o[31]_INST_0_i_6_n_0 ));
  LUT4 #(
    .INIT(16'hFFF8)) 
    \result_o[31]_INST_0_i_7 
       (.I0(\result_o[31]_INST_0_i_20_n_0 ),
        .I1(b_i[2]),
        .I2(\result_o[31]_INST_0_i_21_n_0 ),
        .I3(\result_o[31]_INST_0_i_22_n_0 ),
        .O(\result_o[31]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[31]_INST_0_i_8 
       (.I0(a_i[6]),
        .I1(a_i[14]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .I5(b_i[1]),
        .O(\result_o[31]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[31]_INST_0_i_9 
       (.I0(a_i[10]),
        .I1(a_i[2]),
        .I2(a_i[26]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[18]),
        .O(\result_o[31]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[3]_INST_0 
       (.I0(\result_o[3]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[3]_INST_0_i_2_n_0 ),
        .I3(\result_o[3]_INST_0_i_3_n_0 ),
        .I4(\result_o[3]_INST_0_i_4_n_0 ),
        .I5(\result_o[3]_INST_0_i_5_n_0 ),
        .O(result_o[3]));
  LUT6 #(
    .INIT(64'hFFFFF88888888888)) 
    \result_o[3]_INST_0_i_1 
       (.I0(\result_o[4]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[3]_INST_0_i_6_n_0 ),
        .I3(\result_o[3]_INST_0_i_7_n_0 ),
        .I4(\result_o[3]_INST_0_i_8_n_0 ),
        .I5(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[3]_INST_0_i_1_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[3]_INST_0_i_10 
       (.CI(\<const0> ),
        .CO({\result_o[3]_INST_0_i_10_n_0 ,\result_o[3]_INST_0_i_10_n_1 ,\result_o[3]_INST_0_i_10_n_2 ,\result_o[3]_INST_0_i_10_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[3:0]),
        .O(data0[3:0]),
        .S({\result_o[3]_INST_0_i_16_n_0 ,\result_o[3]_INST_0_i_17_n_0 ,\result_o[3]_INST_0_i_18_n_0 ,\result_o[3]_INST_0_i_19_n_0 }));
  (* SOFT_HLUTNM = "soft_lutpair12" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[3]_INST_0_i_11 
       (.I0(a_i[9]),
        .I1(b_i[4]),
        .I2(b_i[3]),
        .I3(a_i[17]),
        .I4(a_i[25]),
        .O(\result_o[3]_INST_0_i_11_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[3]_INST_0_i_12 
       (.CI(\<const0> ),
        .CO({\result_o[3]_INST_0_i_12_n_0 ,\result_o[3]_INST_0_i_12_n_1 ,\result_o[3]_INST_0_i_12_n_2 ,\result_o[3]_INST_0_i_12_n_3 }),
        .CYINIT(\<const1> ),
        .DI(a_i[3:0]),
        .O(data1[3:0]),
        .S({\result_o[3]_INST_0_i_20_n_0 ,\result_o[3]_INST_0_i_21_n_0 ,\result_o[3]_INST_0_i_22_n_0 ,\result_o[3]_INST_0_i_23_n_0 }));
  LUT5 #(
    .INIT(32'h00000A0C)) 
    \result_o[3]_INST_0_i_13 
       (.I0(a_i[11]),
        .I1(a_i[3]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(b_i[2]),
        .O(\result_o[3]_INST_0_i_13_n_0 ));
  LUT5 #(
    .INIT(32'h0000AC00)) 
    \result_o[3]_INST_0_i_14 
       (.I0(a_i[27]),
        .I1(a_i[19]),
        .I2(b_i[3]),
        .I3(b_i[4]),
        .I4(b_i[2]),
        .O(\result_o[3]_INST_0_i_14_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[3]_INST_0_i_15 
       (.I0(a_i[0]),
        .I1(a_i[2]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[3]_INST_0_i_15_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[3]_INST_0_i_16 
       (.I0(a_i[3]),
        .I1(b_i[3]),
        .O(\result_o[3]_INST_0_i_16_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[3]_INST_0_i_17 
       (.I0(a_i[2]),
        .I1(b_i[2]),
        .O(\result_o[3]_INST_0_i_17_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[3]_INST_0_i_18 
       (.I0(a_i[1]),
        .I1(b_i[1]),
        .O(\result_o[3]_INST_0_i_18_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[3]_INST_0_i_19 
       (.I0(a_i[0]),
        .I1(b_i[0]),
        .O(\result_o[3]_INST_0_i_19_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFF8000C000)) 
    \result_o[3]_INST_0_i_2 
       (.I0(b_i[3]),
        .I1(a_i[3]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(\result_o[3]_INST_0_i_9_n_0 ),
        .O(\result_o[3]_INST_0_i_2_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[3]_INST_0_i_20 
       (.I0(b_i[3]),
        .I1(a_i[3]),
        .O(\result_o[3]_INST_0_i_20_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[3]_INST_0_i_21 
       (.I0(b_i[2]),
        .I1(a_i[2]),
        .O(\result_o[3]_INST_0_i_21_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[3]_INST_0_i_22 
       (.I0(b_i[1]),
        .I1(a_i[1]),
        .O(\result_o[3]_INST_0_i_22_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[3]_INST_0_i_23 
       (.I0(b_i[0]),
        .I1(a_i[0]),
        .O(\result_o[3]_INST_0_i_23_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[3]_INST_0_i_3 
       (.I0(data0[3]),
        .I1(a_i[3]),
        .I2(b_i[3]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[3]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFF88888888888)) 
    \result_o[3]_INST_0_i_4 
       (.I0(\result_o[4]_INST_0_i_9_n_0 ),
        .I1(\result_o[30]_INST_0_i_11_n_0 ),
        .I2(\result_o[3]_INST_0_i_11_n_0 ),
        .I3(\result_o[3]_INST_0_i_7_n_0 ),
        .I4(\result_o[3]_INST_0_i_8_n_0 ),
        .I5(\result_o[30]_INST_0_i_12_n_0 ),
        .O(\result_o[3]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[3]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[3]),
        .O(\result_o[3]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hFF00AAAACCCCF0F0)) 
    \result_o[3]_INST_0_i_6 
       (.I0(a_i[25]),
        .I1(a_i[17]),
        .I2(a_i[9]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[3]_INST_0_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair4" *) 
  LUT2 #(
    .INIT(4'h8)) 
    \result_o[3]_INST_0_i_7 
       (.I0(b_i[1]),
        .I1(b_i[2]),
        .O(\result_o[3]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h33BB33BB33BB3088)) 
    \result_o[3]_INST_0_i_8 
       (.I0(\result_o[5]_INST_0_i_10_n_0 ),
        .I1(b_i[1]),
        .I2(\result_o[7]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(\result_o[3]_INST_0_i_13_n_0 ),
        .I5(\result_o[3]_INST_0_i_14_n_0 ),
        .O(\result_o[3]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'h00000A0000000C00)) 
    \result_o[3]_INST_0_i_9 
       (.I0(\result_o[3]_INST_0_i_15_n_0 ),
        .I1(\result_o[4]_INST_0_i_8_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[3]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[4]_INST_0 
       (.I0(\result_o[4]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[4]_INST_0_i_2_n_0 ),
        .I3(\result_o[4]_INST_0_i_3_n_0 ),
        .I4(\result_o[4]_INST_0_i_4_n_0 ),
        .I5(\result_o[4]_INST_0_i_5_n_0 ),
        .O(result_o[4]));
  (* SOFT_HLUTNM = "soft_lutpair36" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[4]_INST_0_i_1 
       (.I0(\result_o[5]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[4]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[4]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[4]_INST_0_i_10 
       (.I0(a_i[20]),
        .I1(a_i[28]),
        .I2(a_i[4]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[12]),
        .O(\result_o[4]_INST_0_i_10_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[4]_INST_0_i_2 
       (.I0(\result_o[4]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[5]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[4]_INST_0_i_8_n_0 ),
        .O(\result_o[4]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[4]_INST_0_i_3 
       (.I0(data0[4]),
        .I1(a_i[4]),
        .I2(b_i[4]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[4]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[4]_INST_0_i_4 
       (.I0(\result_o[5]_INST_0_i_9_n_0 ),
        .I1(\result_o[4]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[4]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[4]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[4]),
        .O(\result_o[4]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hFF00F0F0CCCCAAAA)) 
    \result_o[4]_INST_0_i_6 
       (.I0(\result_o[4]_INST_0_i_10_n_0 ),
        .I1(\result_o[6]_INST_0_i_10_n_0 ),
        .I2(\result_o[8]_INST_0_i_10_n_0 ),
        .I3(\result_o[10]_INST_0_i_10_n_0 ),
        .I4(b_i[1]),
        .I5(b_i[2]),
        .O(\result_o[4]_INST_0_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair9" *) 
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[4]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[4]),
        .I4(b_i[4]),
        .O(\result_o[4]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[4]_INST_0_i_8 
       (.I0(a_i[1]),
        .I1(a_i[3]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[4]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hFF00F0F0CCCCAAAA)) 
    \result_o[4]_INST_0_i_9 
       (.I0(\result_o[4]_INST_0_i_10_n_0 ),
        .I1(\result_o[6]_INST_0_i_10_n_0 ),
        .I2(\result_o[8]_INST_0_i_12_n_0 ),
        .I3(\result_o[10]_INST_0_i_12_n_0 ),
        .I4(b_i[1]),
        .I5(b_i[2]),
        .O(\result_o[4]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[5]_INST_0 
       (.I0(\result_o[5]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[5]_INST_0_i_2_n_0 ),
        .I3(\result_o[5]_INST_0_i_3_n_0 ),
        .I4(\result_o[5]_INST_0_i_4_n_0 ),
        .I5(\result_o[5]_INST_0_i_5_n_0 ),
        .O(result_o[5]));
  (* SOFT_HLUTNM = "soft_lutpair36" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[5]_INST_0_i_1 
       (.I0(\result_o[6]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[5]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[5]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[5]_INST_0_i_10 
       (.I0(a_i[21]),
        .I1(a_i[29]),
        .I2(a_i[5]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[13]),
        .O(\result_o[5]_INST_0_i_10_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[5]_INST_0_i_2 
       (.I0(\result_o[5]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[6]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[5]_INST_0_i_8_n_0 ),
        .O(\result_o[5]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[5]_INST_0_i_3 
       (.I0(data0[5]),
        .I1(a_i[5]),
        .I2(b_i[5]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[5]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[5]_INST_0_i_4 
       (.I0(\result_o[6]_INST_0_i_9_n_0 ),
        .I1(\result_o[5]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[5]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[5]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[5]),
        .O(\result_o[5]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hFF00F0F0CCCCAAAA)) 
    \result_o[5]_INST_0_i_6 
       (.I0(\result_o[5]_INST_0_i_10_n_0 ),
        .I1(\result_o[7]_INST_0_i_12_n_0 ),
        .I2(\result_o[3]_INST_0_i_6_n_0 ),
        .I3(\result_o[11]_INST_0_i_12_n_0 ),
        .I4(b_i[1]),
        .I5(b_i[2]),
        .O(\result_o[5]_INST_0_i_6_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair10" *) 
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[5]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[5]),
        .I4(b_i[5]),
        .O(\result_o[5]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000F0CCAA)) 
    \result_o[5]_INST_0_i_8 
       (.I0(a_i[4]),
        .I1(a_i[2]),
        .I2(a_i[0]),
        .I3(b_i[1]),
        .I4(b_i[2]),
        .I5(\result_o[30]_INST_0_i_9_n_0 ),
        .O(\result_o[5]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hFF00F0F0CCCCAAAA)) 
    \result_o[5]_INST_0_i_9 
       (.I0(\result_o[5]_INST_0_i_10_n_0 ),
        .I1(\result_o[7]_INST_0_i_12_n_0 ),
        .I2(\result_o[3]_INST_0_i_11_n_0 ),
        .I3(\result_o[11]_INST_0_i_18_n_0 ),
        .I4(b_i[1]),
        .I5(b_i[2]),
        .O(\result_o[5]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[6]_INST_0 
       (.I0(\result_o[6]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[6]_INST_0_i_2_n_0 ),
        .I3(\result_o[6]_INST_0_i_3_n_0 ),
        .I4(\result_o[6]_INST_0_i_4_n_0 ),
        .I5(\result_o[6]_INST_0_i_5_n_0 ),
        .O(result_o[6]));
  (* SOFT_HLUTNM = "soft_lutpair37" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[6]_INST_0_i_1 
       (.I0(\result_o[7]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[6]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[6]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[6]_INST_0_i_10 
       (.I0(a_i[22]),
        .I1(a_i[30]),
        .I2(a_i[6]),
        .I3(b_i[4]),
        .I4(b_i[3]),
        .I5(a_i[14]),
        .O(\result_o[6]_INST_0_i_10_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[6]_INST_0_i_2 
       (.I0(\result_o[6]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[7]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[6]_INST_0_i_8_n_0 ),
        .O(\result_o[6]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[6]_INST_0_i_3 
       (.I0(data0[6]),
        .I1(a_i[6]),
        .I2(b_i[6]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[6]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[6]_INST_0_i_4 
       (.I0(\result_o[7]_INST_0_i_10_n_0 ),
        .I1(\result_o[6]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[6]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[6]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[6]),
        .O(\result_o[6]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[6]_INST_0_i_6 
       (.I0(\result_o[10]_INST_0_i_10_n_0 ),
        .I1(\result_o[12]_INST_0_i_10_n_0 ),
        .I2(\result_o[6]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[8]_INST_0_i_10_n_0 ),
        .O(\result_o[6]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[6]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[6]),
        .I4(b_i[6]),
        .O(\result_o[6]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000F0CCAA)) 
    \result_o[6]_INST_0_i_8 
       (.I0(a_i[5]),
        .I1(a_i[3]),
        .I2(a_i[1]),
        .I3(b_i[1]),
        .I4(b_i[2]),
        .I5(\result_o[30]_INST_0_i_9_n_0 ),
        .O(\result_o[6]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[6]_INST_0_i_9 
       (.I0(\result_o[10]_INST_0_i_12_n_0 ),
        .I1(\result_o[12]_INST_0_i_12_n_0 ),
        .I2(\result_o[6]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[8]_INST_0_i_12_n_0 ),
        .O(\result_o[6]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[7]_INST_0 
       (.I0(\result_o[7]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[7]_INST_0_i_2_n_0 ),
        .I3(\result_o[7]_INST_0_i_3_n_0 ),
        .I4(\result_o[7]_INST_0_i_4_n_0 ),
        .I5(\result_o[7]_INST_0_i_5_n_0 ),
        .O(result_o[7]));
  (* SOFT_HLUTNM = "soft_lutpair37" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[7]_INST_0_i_1 
       (.I0(\result_o[8]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[7]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[7]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[7]_INST_0_i_10 
       (.I0(\result_o[11]_INST_0_i_18_n_0 ),
        .I1(\result_o[13]_INST_0_i_12_n_0 ),
        .I2(\result_o[7]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[3]_INST_0_i_11_n_0 ),
        .O(\result_o[7]_INST_0_i_10_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[7]_INST_0_i_11 
       (.CI(\result_o[3]_INST_0_i_12_n_0 ),
        .CO({\result_o[7]_INST_0_i_11_n_0 ,\result_o[7]_INST_0_i_11_n_1 ,\result_o[7]_INST_0_i_11_n_2 ,\result_o[7]_INST_0_i_11_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[7:4]),
        .O(data1[7:4]),
        .S({\result_o[7]_INST_0_i_18_n_0 ,\result_o[7]_INST_0_i_19_n_0 ,\result_o[7]_INST_0_i_20_n_0 ,\result_o[7]_INST_0_i_21_n_0 }));
  LUT6 #(
    .INIT(64'hFACF0ACFFAC00AC0)) 
    \result_o[7]_INST_0_i_12 
       (.I0(a_i[15]),
        .I1(a_i[23]),
        .I2(b_i[4]),
        .I3(b_i[3]),
        .I4(a_i[31]),
        .I5(a_i[7]),
        .O(\result_o[7]_INST_0_i_12_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[7]_INST_0_i_13 
       (.I0(a_i[4]),
        .I1(a_i[6]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[7]_INST_0_i_13_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[7]_INST_0_i_14 
       (.I0(a_i[7]),
        .I1(b_i[7]),
        .O(\result_o[7]_INST_0_i_14_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[7]_INST_0_i_15 
       (.I0(a_i[6]),
        .I1(b_i[6]),
        .O(\result_o[7]_INST_0_i_15_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[7]_INST_0_i_16 
       (.I0(a_i[5]),
        .I1(b_i[5]),
        .O(\result_o[7]_INST_0_i_16_n_0 ));
  LUT2 #(
    .INIT(4'h6)) 
    \result_o[7]_INST_0_i_17 
       (.I0(a_i[4]),
        .I1(b_i[4]),
        .O(\result_o[7]_INST_0_i_17_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[7]_INST_0_i_18 
       (.I0(b_i[7]),
        .I1(a_i[7]),
        .O(\result_o[7]_INST_0_i_18_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[7]_INST_0_i_19 
       (.I0(b_i[6]),
        .I1(a_i[6]),
        .O(\result_o[7]_INST_0_i_19_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[7]_INST_0_i_2 
       (.I0(\result_o[7]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[8]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[7]_INST_0_i_8_n_0 ),
        .O(\result_o[7]_INST_0_i_2_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[7]_INST_0_i_20 
       (.I0(b_i[5]),
        .I1(a_i[5]),
        .O(\result_o[7]_INST_0_i_20_n_0 ));
  LUT2 #(
    .INIT(4'h9)) 
    \result_o[7]_INST_0_i_21 
       (.I0(b_i[4]),
        .I1(a_i[4]),
        .O(\result_o[7]_INST_0_i_21_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[7]_INST_0_i_3 
       (.I0(data0[7]),
        .I1(a_i[7]),
        .I2(b_i[7]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[7]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[7]_INST_0_i_4 
       (.I0(\result_o[8]_INST_0_i_9_n_0 ),
        .I1(\result_o[7]_INST_0_i_10_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[7]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[7]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[7]),
        .O(\result_o[7]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[7]_INST_0_i_6 
       (.I0(\result_o[11]_INST_0_i_12_n_0 ),
        .I1(\result_o[13]_INST_0_i_10_n_0 ),
        .I2(\result_o[7]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[3]_INST_0_i_6_n_0 ),
        .O(\result_o[7]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[7]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[7]),
        .I4(b_i[7]),
        .O(\result_o[7]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFF44400400)) 
    \result_o[7]_INST_0_i_8 
       (.I0(\result_o[30]_INST_0_i_9_n_0 ),
        .I1(b_i[2]),
        .I2(b_i[1]),
        .I3(a_i[2]),
        .I4(a_i[0]),
        .I5(\result_o[7]_INST_0_i_13_n_0 ),
        .O(\result_o[7]_INST_0_i_8_n_0 ));
  (* ADDER_THRESHOLD = "35" *) 
  CARRY4 \result_o[7]_INST_0_i_9 
       (.CI(\result_o[3]_INST_0_i_10_n_0 ),
        .CO({\result_o[7]_INST_0_i_9_n_0 ,\result_o[7]_INST_0_i_9_n_1 ,\result_o[7]_INST_0_i_9_n_2 ,\result_o[7]_INST_0_i_9_n_3 }),
        .CYINIT(\<const0> ),
        .DI(a_i[7:4]),
        .O(data0[7:4]),
        .S({\result_o[7]_INST_0_i_14_n_0 ,\result_o[7]_INST_0_i_15_n_0 ,\result_o[7]_INST_0_i_16_n_0 ,\result_o[7]_INST_0_i_17_n_0 }));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[8]_INST_0 
       (.I0(\result_o[8]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[8]_INST_0_i_2_n_0 ),
        .I3(\result_o[8]_INST_0_i_3_n_0 ),
        .I4(\result_o[8]_INST_0_i_4_n_0 ),
        .I5(\result_o[8]_INST_0_i_5_n_0 ),
        .O(result_o[8]));
  (* SOFT_HLUTNM = "soft_lutpair38" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[8]_INST_0_i_1 
       (.I0(\result_o[9]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[8]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[8]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'hFF00AAAACCCCF0F0)) 
    \result_o[8]_INST_0_i_10 
       (.I0(a_i[24]),
        .I1(a_i[16]),
        .I2(a_i[8]),
        .I3(a_i[31]),
        .I4(b_i[3]),
        .I5(b_i[4]),
        .O(\result_o[8]_INST_0_i_10_n_0 ));
  LUT6 #(
    .INIT(64'h0000000000000A0C)) 
    \result_o[8]_INST_0_i_11 
       (.I0(a_i[5]),
        .I1(a_i[7]),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[8]_INST_0_i_11_n_0 ));
  (* SOFT_HLUTNM = "soft_lutpair11" *) 
  LUT5 #(
    .INIT(32'h3E0E3202)) 
    \result_o[8]_INST_0_i_12 
       (.I0(a_i[8]),
        .I1(b_i[4]),
        .I2(b_i[3]),
        .I3(a_i[16]),
        .I4(a_i[24]),
        .O(\result_o[8]_INST_0_i_12_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[8]_INST_0_i_2 
       (.I0(\result_o[8]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[9]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[8]_INST_0_i_8_n_0 ),
        .O(\result_o[8]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[8]_INST_0_i_3 
       (.I0(data0[8]),
        .I1(a_i[8]),
        .I2(b_i[8]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[8]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[8]_INST_0_i_4 
       (.I0(\result_o[9]_INST_0_i_9_n_0 ),
        .I1(\result_o[8]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[8]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[8]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[8]),
        .O(\result_o[8]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[8]_INST_0_i_6 
       (.I0(\result_o[12]_INST_0_i_10_n_0 ),
        .I1(\result_o[14]_INST_0_i_10_n_0 ),
        .I2(\result_o[8]_INST_0_i_10_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[10]_INST_0_i_10_n_0 ),
        .O(\result_o[8]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[8]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[8]),
        .I4(b_i[8]),
        .O(\result_o[8]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFF44400400)) 
    \result_o[8]_INST_0_i_8 
       (.I0(\result_o[30]_INST_0_i_9_n_0 ),
        .I1(b_i[2]),
        .I2(b_i[1]),
        .I3(a_i[3]),
        .I4(a_i[1]),
        .I5(\result_o[8]_INST_0_i_11_n_0 ),
        .O(\result_o[8]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[8]_INST_0_i_9 
       (.I0(\result_o[12]_INST_0_i_12_n_0 ),
        .I1(\result_o[14]_INST_0_i_12_n_0 ),
        .I2(\result_o[8]_INST_0_i_12_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[10]_INST_0_i_12_n_0 ),
        .O(\result_o[8]_INST_0_i_9_n_0 ));
  LUT6 #(
    .INIT(64'hFFFFFFFFEEEEEEEA)) 
    \result_o[9]_INST_0 
       (.I0(\result_o[9]_INST_0_i_1_n_0 ),
        .I1(\result_o[30]_INST_0_i_2_n_0 ),
        .I2(\result_o[9]_INST_0_i_2_n_0 ),
        .I3(\result_o[9]_INST_0_i_3_n_0 ),
        .I4(\result_o[9]_INST_0_i_4_n_0 ),
        .I5(\result_o[9]_INST_0_i_5_n_0 ),
        .O(result_o[9]));
  (* SOFT_HLUTNM = "soft_lutpair38" *) 
  LUT4 #(
    .INIT(16'hF888)) 
    \result_o[9]_INST_0_i_1 
       (.I0(\result_o[10]_INST_0_i_6_n_0 ),
        .I1(\result_o[30]_INST_0_i_7_n_0 ),
        .I2(\result_o[9]_INST_0_i_6_n_0 ),
        .I3(\result_o[30]_INST_0_i_10_n_0 ),
        .O(\result_o[9]_INST_0_i_1_n_0 ));
  LUT6 #(
    .INIT(64'h000000000000AC00)) 
    \result_o[9]_INST_0_i_10 
       (.I0(a_i[2]),
        .I1(a_i[4]),
        .I2(b_i[1]),
        .I3(b_i[2]),
        .I4(b_i[4]),
        .I5(b_i[3]),
        .O(\result_o[9]_INST_0_i_10_n_0 ));
  LUT5 #(
    .INIT(32'hFFEAEAEA)) 
    \result_o[9]_INST_0_i_2 
       (.I0(\result_o[9]_INST_0_i_7_n_0 ),
        .I1(\result_o[31]_INST_0_i_11_n_0 ),
        .I2(\result_o[10]_INST_0_i_8_n_0 ),
        .I3(\result_o[30]_INST_0_i_15_n_0 ),
        .I4(\result_o[9]_INST_0_i_8_n_0 ),
        .O(\result_o[9]_INST_0_i_2_n_0 ));
  LUT6 #(
    .INIT(64'h00FC0000003C00AA)) 
    \result_o[9]_INST_0_i_3 
       (.I0(data0[9]),
        .I1(a_i[9]),
        .I2(b_i[9]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[2]),
        .I5(alu_op_i[1]),
        .O(\result_o[9]_INST_0_i_3_n_0 ));
  LUT6 #(
    .INIT(64'h0000A0000000C000)) 
    \result_o[9]_INST_0_i_4 
       (.I0(\result_o[10]_INST_0_i_9_n_0 ),
        .I1(\result_o[9]_INST_0_i_9_n_0 ),
        .I2(alu_op_i[2]),
        .I3(alu_op_i[0]),
        .I4(alu_op_i[1]),
        .I5(b_i[0]),
        .O(\result_o[9]_INST_0_i_4_n_0 ));
  LUT6 #(
    .INIT(64'h0000000200000000)) 
    \result_o[9]_INST_0_i_5 
       (.I0(alu_op_i[3]),
        .I1(alu_op_i[4]),
        .I2(alu_op_i[1]),
        .I3(alu_op_i[2]),
        .I4(alu_op_i[0]),
        .I5(data1[9]),
        .O(\result_o[9]_INST_0_i_5_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[9]_INST_0_i_6 
       (.I0(\result_o[13]_INST_0_i_10_n_0 ),
        .I1(\result_o[15]_INST_0_i_12_n_0 ),
        .I2(\result_o[3]_INST_0_i_6_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[11]_INST_0_i_12_n_0 ),
        .O(\result_o[9]_INST_0_i_6_n_0 ));
  LUT5 #(
    .INIT(32'hC0004000)) 
    \result_o[9]_INST_0_i_7 
       (.I0(alu_op_i[0]),
        .I1(alu_op_i[2]),
        .I2(alu_op_i[1]),
        .I3(a_i[9]),
        .I4(b_i[9]),
        .O(\result_o[9]_INST_0_i_7_n_0 ));
  LUT6 #(
    .INIT(64'hAAAEAFAEAAAEAAAE)) 
    \result_o[9]_INST_0_i_8 
       (.I0(\result_o[9]_INST_0_i_10_n_0 ),
        .I1(\result_o[15]_INST_0_i_13_n_0 ),
        .I2(b_i[2]),
        .I3(b_i[1]),
        .I4(\result_o[30]_INST_0_i_9_n_0 ),
        .I5(a_i[6]),
        .O(\result_o[9]_INST_0_i_8_n_0 ));
  LUT6 #(
    .INIT(64'hCCFFAAF0CC00AAF0)) 
    \result_o[9]_INST_0_i_9 
       (.I0(\result_o[13]_INST_0_i_12_n_0 ),
        .I1(\result_o[15]_INST_0_i_18_n_0 ),
        .I2(\result_o[3]_INST_0_i_11_n_0 ),
        .I3(b_i[2]),
        .I4(b_i[1]),
        .I5(\result_o[11]_INST_0_i_18_n_0 ),
        .O(\result_o[9]_INST_0_i_9_n_0 ));
endmodule
