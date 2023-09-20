module rf_riscv(
  input  logic        clk_i,
  input  logic        write_enable_i,

  input  logic [ 4:0] write_addr_i,
  input  logic [ 4:0] read_addr1_i,
  input  logic [ 4:0] read_addr2_i,

  input  logic [31:0] write_data_i,
  output logic [31:0] read_data1_o,
  output logic [31:0] read_data2_o
);

`define akjsdnnaskjdnreg  $clog2(128)
`define cdyfguvhbjnmkreg  $clog2(`akjsdnnaskjdnreg)
`define qwenklfsaklasdreg $clog2(`cdyfguvhbjnmkreg)
`define asdasdhkjasdsareg (34 >> `cdyfguvhbjnmkreg)

logic [(`asdasdhkjasdsareg<<`qwenklfsaklasdreg)+15:0] rf_mem [`asdasdhkjasdsareg*8];

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
