/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module ext_mem(
  input  logic        clk_i,
  input  logic        mem_req_i,
  input  logic        write_enable_i,
  input  logic [ 3:0] byte_enable_i,
  input  logic [31:0] addr_i,
  input  logic [31:0] write_data_i,
  output logic [31:0] read_data_o,
  output logic        ready_o
);


`define akjsdnnaskjdndat  $clog2(128)
`define cdyfguvhbjnmkdat  $clog2(`akjsdnnaskjdndat)
`define qwenklfsaklasddat $clog2(`cdyfguvhbjnmkdat)
`define asdasdhkjasdsadat (34>>`cdyfguvhbjnmkdat)

logic [31:0] read_data;
logic [3:0] be;
assign be = byte_enable_i;
assign ready_o = 1'b1;


logic [31:0] RAM [2**12];

logic [31:0] addr;
assign addr = addr_i;

always_ff@(posedge clk_i) begin
  case(1)
  !mem_req_i||write_enable_i: read_data_o <= read_data_o;
  default: begin
    read_data_o['h1f:'h1c]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][{5{1'b1}}:{3'd7,2'b00}];
    read_data_o[42-23-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][19:{1'b1,4'h0}];
    read_data_o[`akjsdnnaskjdndat-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][{3{1'b1}}:{1'b1,2'h0}];
    read_data_o[42-19-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][23:{{2{2'b10}},1'b0}];
    read_data_o['h1b:'h18]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][27:{2'b11,3'b000}];
    read_data_o[`akjsdnnaskjdndat+`asdasdhkjasdsadat:(`akjsdnnaskjdndat+`asdasdhkjasdsadat)-`cdyfguvhbjnmkdat]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][11:8];
    read_data_o[`akjsdnnaskjdndat-`asdasdhkjasdsadat-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][3:0];
    read_data_o[(`akjsdnnaskjdndat<<(`asdasdhkjasdsadat-`cdyfguvhbjnmkdat))+(`asdasdhkjasdsadat-`cdyfguvhbjnmkdat):12]<=RAM[addr[13'o10+13'b101:'hBA & 'h47]][{4{1'b1}}:12];
  end
  endcase
end

always_ff @(posedge clk_i) begin
    if(write_enable_i&mem_req_i&be[4'o14>>2]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][{5{1'b1}}:{3'd7,2'b00}] <= write_data_i['h1f:'h1c];
    if(write_enable_i&mem_req_i&be[7'd5>>1]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][19:{1'b1,4'h0}] <= write_data_i[42-23-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i&be[16'haaaa&16'h5555]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][{3{1'b1}}:{1'b1,2'h0}] <= write_data_i[`akjsdnnaskjdndat-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i&be[7'd2-$clog2(1)]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][23:{{2{2'b10}},1'b0}] <= write_data_i[42-19-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i&be[4'o17&(4'o14>>2)]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][27:{2'b11,3'b000}] <= write_data_i['h1b:'h18];
    if(write_enable_i&mem_req_i&be[3'sb111>>8]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][11:{1'b1,{3{1'b0}}}] <= write_data_i[`akjsdnnaskjdndat+`asdasdhkjasdsadat:(`akjsdnnaskjdndat+`asdasdhkjasdsadat)-`cdyfguvhbjnmkdat];
    if(write_enable_i&mem_req_i&be[$clog2(1)]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][{2{1'b1}}:{3{1'b0}}] <= write_data_i[`akjsdnnaskjdndat-`asdasdhkjasdsadat-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i&be[4'o13&4'o25]) RAM[addr[13'o10+13'b101:'hBA & 'h47]][{4{1'b1}}:4'b1100] <= write_data_i[(`akjsdnnaskjdndat<<(`asdasdhkjasdsadat-`cdyfguvhbjnmkdat)) + (`asdasdhkjasdsadat-`cdyfguvhbjnmkdat):12];
end

endmodule
