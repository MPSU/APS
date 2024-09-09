/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module lab_08_tb_lsu();
import decoder_pkg::*;
logic        clk_i        ;
logic        rst_i        ;
logic        core_req_i   ;
logic        core_we_i    ;
logic [ 2:0] core_size_i  ;
logic [31:0] core_addr_i  ;
logic [31:0] core_wd_i    ;
logic [31:0] core_rd_o    ;
logic        core_stall_o ;
logic        mem_req_o    ;
logic        mem_we_o     ;
logic [ 3:0] mem_be_o     ;
logic [31:0] mem_addr_o   ;
logic [31:0] mem_wd_o     ;
logic [31:0] mem_rd_i     ;
logic        mem_ready_i  ;
logic        grm_req_o    ;
logic [31:0] grm_rd_o     ;
logic        grm_stall_o  ;
logic        grm_we_o     ;
logic [ 3:0] grm_be_o     ;
logic [31:0] grm_addr_o   ;
logic [31:0] grm_wd_o     ;
lsu dut(.*);

lsu_ref grm(
    .core_rd_o      (grm_rd_o   ),
    .core_stall_o   (grm_stall_o),
    .mem_we_o       (grm_we_o   ),
    .mem_be_o       (grm_be_o   ),
    .mem_addr_o     (grm_addr_o ),
    .mem_wd_o       (grm_wd_o   ),
    .mem_req_o      (grm_req_o  ),
    .*
);



always #5 clk_i <= ~clk_i;

int err_count;
bit not_stopped;
initial begin
  $display("Test has been started.");
  err_count = 0;
  not_stopped = 1;
  clk_i <= 0;
  rst_i <= 1'b1;
  repeat(2)@(posedge clk_i);
  rst_i <= 1'b0;
  repeat(3e3)@(posedge clk_i);
  $display("Simulation finished. Number of errors: %d", err_count);
  $finish();
  #5;
  $display("You're trying to run simulation that has finished. Aborting simulation.")
  $fatal();
end

initial begin
  core_req_i   = '0;
  core_we_i    = '0;
  core_size_i  = '0;
  core_addr_i  = '0;
  core_wd_i    = '0;
  mem_rd_i     = '0;
  mem_ready_i  = '0;
  repeat(4)@(posedge clk_i);
  forever begin
  if((err_count >= 10) && not_stopped) begin
    $display("Simulation stopped after ten errors.");
    $stop();
    not_stopped = 0;
  end
  @(posedge clk_i);
    if(!core_stall_o) begin
      core_req_i    = $random;
      core_we_i     = $random;
      if(core_we_i) begin
        assert(std::randomize(core_size_i) with {core_size_i inside {LDST_B,LDST_H,LDST_W};});
      end else begin
        assert(std::randomize(core_size_i) with {core_size_i inside {LDST_B,LDST_H,LDST_W,LDST_BU,LDST_HU};});
      end
      core_addr_i   = $random;
      core_wd_i     = $random;
      mem_rd_i      = $random;
    end
    mem_ready_i     = $random;
  end
end

logic is_reading, is_writing;
assign is_reading = core_req_i && !core_we_i;
assign is_writing = core_req_i &&  core_we_i;

stall_seq: assert property (
  @(posedge clk_i)
    disable iff ( rst_i )
  core_req_i |-> (core_stall_o || $past(core_stall_o))
)else begin
        err_count++;
        $error("\nIncorrect implementation of core_stall_o signal\n");
    end

stall_rise: assert property (
  @(posedge clk_i)
    disable iff ( rst_i )
  $rose(core_req_i) |-> $rose(core_stall_o)
)else begin
        err_count++;
        $error("\nRising core_req_i means rising core_stall_o\n");
    end

stall_fall: assert property (
  @(posedge clk_i)
    disable iff ( rst_i )
  $fell(core_req_i) |-> !core_stall_o
)else begin
        err_count++;
        $error("\nFalling core_req_i can be only on !core_stall_o\n");
    end

stall: assert property (
  @(posedge clk_i)
    disable iff ( rst_i )
  core_stall_o |-> core_req_i
)else begin
        err_count++;
        $error("\ncore_stall_o can be asserted only while core_req_i == 1\n");
    end

stall_rst: assert property (
  @(posedge clk_i)
  (rst_i) |=> !core_stall_o
)else begin
        err_count++;
        $error("\nrst_i should reset core_stall_o and it's register\n");
    end

mem_we: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  mem_we_o === core_we_i
)else begin
        err_count++;
        $error("\nmem_we_o should be equal core_we_i\n");
    end

mem_req: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  mem_req_o === core_req_i
)else begin
        err_count++;
        $error("\nmem_req_o should be equal core_req_i\n");
    end

mem_addr: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  core_req_i |-> (mem_addr_o === core_addr_i)
)else begin
        err_count++;
        $error("\nmem_addr_o should be equal core_addr_i\n");
    end

core_rdata: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  is_reading |-> (core_rd_o === grm_rd_o)
)else begin
        err_count++;
        $error("\nIncorrect value of core_rd_o. Your value is %0h while it should be %0h", core_rd_o, grm_rd_o);
    end

core_stall: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  core_stall_o === grm_stall_o
)else begin
        err_count++;
        $error("\nIncorrect value of core_stall_o. Your value is %0h while it should be %0h", core_stall_o, grm_stall_o);
    end

mem_be: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  is_writing |-> (mem_be_o === grm_be_o)
)else begin
        err_count++;
        $error("\nIncorrect value of mem_be_o. Your value is %0h while it should be %0h", mem_be_o, grm_be_o);
    end

mem_wdata: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  is_writing |-> mem_wd_o === grm_wd_o
)else begin
        err_count++;
        $error("\nIncorrect value of mem_wd_o. Your value is %0h while it should be %0h", mem_wd_o, grm_wd_o);
    end

endmodule

module lsu_ref(
  input logic clk_i,
  input logic rst_i,

  // Интерфейс с ядром
  input  logic        core_req_i,
  input  logic        core_we_i,
  input  logic [ 2:0] core_size_i,
  input  logic [31:0] core_addr_i,
  input  logic [31:0] core_wd_i,
  output logic [31:0] core_rd_o,
  output logic        core_stall_o,

  // Интерфейс с памятью
  output logic        mem_req_o,
  output logic        mem_we_o,
  output logic [ 3:0] mem_be_o,
  output logic [31:0] mem_addr_o,
  output logic [31:0] mem_wd_o,
  input  logic [31:0] mem_rd_i,
  input  logic        mem_ready_i
);

import decoder_pkg::*;
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
