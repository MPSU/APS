/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module data_mem (
  input  logic        clk_i,
  input  logic        mem_req_i,
  input  logic        write_enable_i,
  input  logic [ 3:0] byte_enable_i,
  input  logic [31:0] addr_i,
  input  logic [31:0] write_data_i,
  output logic [31:0] read_data_o,
  output logic        ready_o
);
assign ready_o = 1'b1;
import memory_pkg::DATA_MEM_SIZE_WORDS;
logic [31:0] ram [DATA_MEM_SIZE_WORDS];

logic [31:0] addr;
assign addr = addr_i[2+:$clog2(DATA_MEM_SIZE_WORDS)];

always_ff @(posedge clk_i) begin
  if(mem_req_i & !write_enable_i) begin
    read_data_o <= ram[addr];
  end
end

always_ff @(posedge clk_i) begin
  if(mem_req_i & write_enable_i) begin
    if(byte_enable_i[0]) ram[addr][ 7: 0] = write_data_i[ 7: 0];
    if(byte_enable_i[1]) ram[addr][15: 8] = write_data_i[15: 8];
    if(byte_enable_i[2]) ram[addr][23:16] = write_data_i[23:16];
    if(byte_enable_i[3]) ram[addr][31:24] = write_data_i[31:24];
  end
end

endmodule
