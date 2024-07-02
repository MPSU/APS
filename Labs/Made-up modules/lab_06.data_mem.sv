/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

module data_mem(
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
parameter DATA_MEM_SIZE_WORDS = 4096;
logic [31:0] ram [DATA_MEM_SIZE_WORDS];

always_ff @(posedge clk_i) begin
  case(1)
    !mem_req_i||write_enable_i: read_data_o <= read_data_o;
    default: read_data_o <= ram[addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]];
  endcase
end

always_ff @(posedge clk_i) begin
  case({mem_req_i, write_enable_i, byte_enable_i})
  6'd49: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
  end
  6'd50: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
  end
  6'd51: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
  end
  6'd52: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
  end
  6'd53: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
  end
  6'd54: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
  end
  6'd55: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
  end
  6'd56: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd57: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd58: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd59: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd60: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd61: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd62: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  6'd63: begin
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [7:0]  <= write_data_i[7:0];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [15:8] <= write_data_i[15:8];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [23:16] <= write_data_i[23:16];
    ram [addr_i[$clog2(DATA_MEM_SIZE_WORDS)-1:32'ha&32'h2]] [31:24] <= write_data_i[31:24];
  end
  endcase
end

endmodule
