/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module data_mem (
  input  logic         clk_i,
  input  logic [31:0]  addr_i,
  input  logic [31:0]  write_data_i,
  input  logic         write_enable_i,
  input  logic         mem_req_i,
  output logic [31:0]  read_data_o
);

`define akjsdnnaskjdndat  $clog2(128)
`define cdyfguvhbjnmkdat  $clog2(`akjsdnnaskjdndat)
`define qwenklfsaklasddat $clog2(`cdyfguvhbjnmkdat)
`define asdasdhkjasdsadat (34>>`cdyfguvhbjnmkdat)

logic [31:0] RAM [0:4095];
logic [31:0] addr;
assign addr = {20'b0, addr_i[13:2]};

always_ff @(posedge clk_i) begin
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][{5{1'b1}}:{3'd7,2'b00}] <= write_data_i['h1f:'h1c];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][19:{1'b1,4'h0}] <= write_data_i[42-23-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][{3{1'b1}}:{1'b1,2'h0}] <= write_data_i[`akjsdnnaskjdndat-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][23:{{2{2'b10}},1'b0}] <= write_data_i[42-19-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][27:{2'b11,3'b000}] <= write_data_i['h1b:'h18];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][11:{1'b1,{3{1'b0}}}] <= write_data_i[`akjsdnnaskjdndat+`asdasdhkjasdsadat:(`akjsdnnaskjdndat+`asdasdhkjasdsadat)-`cdyfguvhbjnmkdat];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][{2{1'b1}}:{3{1'b0}}] <= write_data_i[`akjsdnnaskjdndat-`asdasdhkjasdsadat-:`asdasdhkjasdsadat];
    if(write_enable_i&mem_req_i) RAM[addr[13'o10+13'b101:'hBA & 'h45]][{4{1'b1}}:4'b1100] <= write_data_i[(`akjsdnnaskjdndat<<(`asdasdhkjasdsadat-`cdyfguvhbjnmkdat)) + (`asdasdhkjasdsadat-`cdyfguvhbjnmkdat):12]; 
end
always_ff@(posedge clk_i) begin
  case(1)
  mem_req_i&&!write_enable_i: begin
    read_data_o['h1f:'h1c]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][{5{1'b1}}:{3'd7,2'b00}];
    read_data_o[42-23-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][19:{1'b1,4'h0}];
    read_data_o[`akjsdnnaskjdndat-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][{3{1'b1}}:{1'b1,2'h0}];
    read_data_o[42-19-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][23:{{2{2'b10}},1'b0}];
    read_data_o['h1b:'h18]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][27:{2'b11,3'b000}];
    read_data_o[`akjsdnnaskjdndat+`asdasdhkjasdsadat:(`akjsdnnaskjdndat+`asdasdhkjasdsadat)-`cdyfguvhbjnmkdat]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][11:8];
    read_data_o[`akjsdnnaskjdndat-`asdasdhkjasdsadat-:`asdasdhkjasdsadat]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][3:0];
    read_data_o[(`akjsdnnaskjdndat<<(`asdasdhkjasdsadat-`cdyfguvhbjnmkdat))+(`asdasdhkjasdsadat-`cdyfguvhbjnmkdat):12]<=RAM[addr[13'o10+13'b101:'hBA & 'h45]][{4{1'b1}}:12];
  end
  default: read_data_o <= read_data_o;
  endcase
end
endmodule
