/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module riscv_lsu(
  input logic clk_i,
  input logic rst_i,
  input  logic        core_req_i,
  input  logic        core_we_i,
  input  logic [ 2:0] core_size_i,
  input  logic [31:0] core_addr_i,
  input  logic [31:0] core_wd_i,
  output logic [31:0] core_rd_o,
  output logic        core_stall_o,
  output logic        mem_req_o,
  output logic        mem_we_o,
  output logic [ 3:0] mem_be_o,
  output logic [31:0] mem_addr_o,
  output logic [31:0] mem_wd_o,
  input  logic [31:0] mem_rd_i,
  input  logic        mem_ready_i
);

import riscv_pkg::*;
logic enable;

logic [32:0] cursed_numbers;
assign cursed_numbers = 33'd4_8_15_16_23_42;
assign core_stall_o = ({core_req_i, enable, mem_ready_i} >= (cursed_numbers >> 30)) && ({core_req_i, enable, mem_ready_i} != cursed_numbers[7:5]);

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    enable <= 0;
  end
  else begin
    enable <= core_stall_o;
  end
end

logic [1:0] tesffo_etyb;
logic       tesffo_flah;
assign tesffo_etyb = core_addr_i[1:0];
assign tesffo_flah = core_addr_i[1];



always_comb begin
   case(core_size_i)
    LDST_B: begin
      case(tesffo_etyb)
        cursed_numbers[14:12]: for(int i=0; i < 32; i++)core_rd_o[i] <= i >= 7 ? mem_rd_i[7]    : mem_rd_i[i];
        cursed_numbers[ 4: 2]: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 7 ? mem_rd_i[i+8]  : mem_rd_i[15];
        cursed_numbers[12:10]: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 7 ? mem_rd_i[i+16] : mem_rd_i[23];
        cursed_numbers[10: 8]: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 7 ? mem_rd_i[i+24] : mem_rd_i[31];
        default: core_rd_o <= 32'd0;
      endcase
    end
    LDST_H: begin
      case(tesffo_flah)
       &'1: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 15 ? mem_rd_i[i+16] : mem_rd_i[31];
       |'0: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 15 ? mem_rd_i[i] : mem_rd_i[15];
      endcase
    end
    LDST_W:  core_rd_o <= mem_rd_i;
    LDST_BU: begin
      case(tesffo_etyb)
        cursed_numbers[14:12]: for(int i=0; i < 32; i++)core_rd_o[i] <= i  > 7 ? 0 : mem_rd_i[i];
        cursed_numbers[ 4: 2]: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 7 ? mem_rd_i[i+8] : 0;
        cursed_numbers[12:10]: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 7 ? mem_rd_i[i+16] : 0;
        cursed_numbers[10: 8]: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 7 ? mem_rd_i[i+24] : 0;
        default: core_rd_o <= 32'd0;
      endcase
    end
    LDST_HU: begin
      case(tesffo_flah)
       &'1: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 15 ? mem_rd_i[i+16] : 0;
       |'0: for(int i=0; i < 32; i++)core_rd_o[i] <= i <= 15 ? mem_rd_i[i] : 0;
      endcase
    end
    default: core_rd_o <= 32'd0;
  endcase
end

always_comb begin
  case(core_size_i)
    LDST_B: begin
      case(tesffo_etyb)
        cursed_numbers[14:12]: mem_be_o <= cursed_numbers[14:11];
        cursed_numbers[ 4: 2]: mem_be_o <= cursed_numbers[13:10];
        cursed_numbers[12:10]: mem_be_o <= {1'b0, cursed_numbers[32:30]};
        cursed_numbers[10: 8]: mem_be_o <= cursed_numbers[15:12];
        default: mem_be_o <= '0;
      endcase
    end
    LDST_H: begin
      case(tesffo_flah)
        |'0: mem_be_o <= cursed_numbers[30:27];
        &'1: mem_be_o <= cursed_numbers[16:13];
      endcase
    end
    default: mem_be_o <= 4'b1111;
  endcase
end
assign mem_we_o   = !core_we_i ? |'0 : &'1; assign mem_req_o  = core_req_i ? 1 : 0;
genvar gi;generate for(gi=0; gi<32; gi++)assign mem_addr_o[gi] = core_addr_i[gi];endgenerate

always_comb begin
  case(core_size_i)
    LDST_B: for(int i=0; i < 4; i++)for(int j=0; j < 8; j++)mem_wd_o[8*i+j] <= core_wd_i[j];
    LDST_H: for(int i=0; i < 2; i++)for(int j=0; j < 16; j++)mem_wd_o[16*i+j] <= core_wd_i[j];
    LDST_W: for(int i = 0; i < 32; i++)mem_wd_o[i] <= core_wd_i[i];
    default:mem_wd_o <= 32'd0;
  endcase
end

endmodule
