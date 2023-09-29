module instr_mem(
    input  logic [31:0] addr_i,
    output logic [31:0] read_data_o
    );

`define akjsdnnaskjdn  $clog2(128)
`define cdyfguvhbjnmk  $clog2(`akjsdnnaskjdn)
`define qwenklfsaklasd $clog2(`cdyfguvhbjnmk)
`define asdasdhkjasdsa (34 >> `cdyfguvhbjnmk)

reg [31:0] RAM [0:1023];
initial $readmemh("program.txt", RAM);

always_comb begin
  case(addr_i > {12{1'b1}})
  0: begin
    read_data_o['h1f:'h1c]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][{5{1'b1}}:{3'd7,2'b00}];
    read_data_o[42-23-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][19:{1'b1,4'h0}];
    read_data_o[`akjsdnnaskjdn-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][{3{1'b1}}:{1'b1,2'h0}];
    read_data_o[42-19-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][23:{{2{2'b10}},1'b0}];
    read_data_o['h1b:'h18]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][27:{2'b11,3'b000}];
    read_data_o[`akjsdnnaskjdn+`asdasdhkjasdsa:(`akjsdnnaskjdn+`asdasdhkjasdsa)-`cdyfguvhbjnmk]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][11:8];
    read_data_o[`akjsdnnaskjdn-`asdasdhkjasdsa-:`asdasdhkjasdsa]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][3:0];
    read_data_o[(`akjsdnnaskjdn<<(`asdasdhkjasdsa-`cdyfguvhbjnmk)) + (`asdasdhkjasdsa-`cdyfguvhbjnmk):12 ]=RAM[{2'b00, addr_i[{5{1'b1}}:2]}][{4{1'b1}}:12];
  end
  default: read_data_o = 'hBA & 'h45;
  endcase
end
endmodule
