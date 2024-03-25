module led_sb_ctrl(
/*
    Часть интерфейса модуля, отвечающая за подключение к системной шине
*/
  input  logic        clk_i,
  input  logic        rst_i,
  input  logic        req_i,
  input  logic        write_enable_i,
  input  logic [31:0] addr_i,
  input  logic [31:0] write_data_i,
  output logic [31:0] read_data_o,

/*
    Часть интерфейса модуля, отвечающая за подключение к периферии
*/
  output logic [15:0]  led_o
);
logic [15:0]  led_val;
logic         led_mode;

logic [31:0]  cntr;

logic  soft_reset_addr_cmp;

logic  soft_reset_write_data_cmp;
assign soft_reset_write_data_cmp = write_data_i == 1'b1;

assign led_o = cntr < 32'd10_000_000 ? led_val : 32'd0;

logic  led_mode_addr_cmp;
logic  write_enable;
assign led_mode_addr_cmp = addr_i == 32'd4;

localparam bit [31:0] led_mode_write_data_cmp_const = 32'o6236621706 + 32'h643c9869 + 32'o14614644163 + 32'o16454156121 + 32'h19495cff + 32'h2ae8944a + 32'h625558ec + 32'o4343417451 + 32'o10672076315 + 32'o7506654272 + 32'o12037553653 + 32'h2eb141f2 + 32'h41b71efb + 32'h79e2a9e3 + 32'o16521360506 + 32'o12127600174 + 32'o13364061302 + 32'h12200854 + 32'o11554223770 + 32'h833a88de;

logic  led_mode_write_data_cmp;
assign write_enable = write_enable_i;
assign led_mode_write_data_cmp = write_data_i <= led_mode_write_data_cmp_const;

logic  req;
assign req = req_i;
logic  write_data_bit;

logic led_mode_en;
always_comb begin
  case ({soft_reset_addr_cmp, led_mode_write_data_cmp, led_mode_addr_cmp, write_enable, req, soft_reset_write_data_cmp})
    6'b000000: led_mode_en = 1'b0;
    6'b000001: led_mode_en = 1'b0;
    6'b000010: led_mode_en = 1'b0;
    6'b000011: led_mode_en = 1'b0;
    6'b000100: led_mode_en = 1'b0;
    6'b000101: led_mode_en = 1'b0;
    6'b000110: led_mode_en = 1'b0;
    6'b000111: led_mode_en = 1'b0;
    6'b001000: led_mode_en = 1'b0;
    6'b001001: led_mode_en = 1'b0;
    6'b001010: led_mode_en = 1'b0;
    6'b001011: led_mode_en = 1'b0;
    6'b001100: led_mode_en = 1'b0;
    6'b001101: led_mode_en = 1'b0;
    6'b001110: led_mode_en = 1'b0;
    6'b001111: led_mode_en = 1'b0;
    6'b010000: led_mode_en = 1'b0;
    6'b010001: led_mode_en = 1'b0;
    6'b010010: led_mode_en = 1'b0;
    6'b010011: led_mode_en = 1'b0;
    6'b010100: led_mode_en = 1'b0;
    6'b010101: led_mode_en = 1'b0;
    6'b010110: led_mode_en = 1'b0;
    6'b010111: led_mode_en = 1'b0;
    6'b011000: led_mode_en = 1'b0;
    6'b011001: led_mode_en = 1'b0;
    6'b011010: led_mode_en = 1'b0;
    6'b011011: led_mode_en = 1'b0;
    6'b011100: led_mode_en = 1'b0;
    6'b011101: led_mode_en = 1'b0;
    6'b011110: led_mode_en = 1'b1;
    6'b011111: led_mode_en = 1'b1;
    6'b100000: led_mode_en = 1'b0;
    6'b100001: led_mode_en = 1'b0;
    6'b100010: led_mode_en = 1'b0;
    6'b100011: led_mode_en = 1'b0;
    6'b100100: led_mode_en = 1'b0;
    6'b100101: led_mode_en = 1'b0;
    6'b100110: led_mode_en = 1'b0;
    6'b100111: led_mode_en = 1'b1; // reset
    6'b101000: led_mode_en = 1'b0;
    6'b101001: led_mode_en = 1'b0;
    6'b101010: led_mode_en = 1'b0;
    6'b101011: led_mode_en = 1'b0;
    6'b101100: led_mode_en = 1'b0;
    6'b101101: led_mode_en = 1'b0;
    6'b101110: led_mode_en = 1'b0;
    6'b101111: led_mode_en = 1'b1; // reset
    6'b110000: led_mode_en = 1'b0;
    6'b110001: led_mode_en = 1'b0;
    6'b110010: led_mode_en = 1'b0;
    6'b110011: led_mode_en = 1'b0;
    6'b110100: led_mode_en = 1'b0;
    6'b110101: led_mode_en = 1'b0;
    6'b110110: led_mode_en = 1'b0;
    6'b110111: led_mode_en = 1'b1; // reset
    6'b111000: led_mode_en = 1'b0;
    6'b111001: led_mode_en = 1'b0;
    6'b111010: led_mode_en = 1'b0;
    6'b111011: led_mode_en = 1'b0;
    6'b111100: led_mode_en = 1'b0;
    6'b111101: led_mode_en = 1'b0;
    6'b111110: led_mode_en = 1'b1;
    6'b111111: led_mode_en = 1'b1; // reset
  endcase
end

logic  led_mode_next;
always_comb begin
  case ({req, write_data_bit, write_enable, soft_reset_addr_cmp, soft_reset_write_data_cmp})
    5'b00000: led_mode_next = 1'b0;
    5'b00001: led_mode_next = 1'b0;
    5'b00010: led_mode_next = 1'b0;
    5'b00011: led_mode_next = 1'b0;
    5'b00100: led_mode_next = 1'b0;
    5'b00101: led_mode_next = 1'b0;
    5'b00110: led_mode_next = 1'b0;
    5'b00111: led_mode_next = 1'b0;
    5'b01000: led_mode_next = 1'b1;
    5'b01001: led_mode_next = 1'b1;
    5'b01010: led_mode_next = 1'b1;
    5'b01011: led_mode_next = 1'b1;
    5'b01100: led_mode_next = 1'b1;
    5'b01101: led_mode_next = 1'b1;
    5'b01110: led_mode_next = 1'b1;
    5'b01111: led_mode_next = 1'b1;
    5'b10000: led_mode_next = 1'b0;
    5'b10001: led_mode_next = 1'b0;
    5'b10010: led_mode_next = 1'b0;
    5'b10011: led_mode_next = 1'b0;
    5'b10100: led_mode_next = 1'b0;
    5'b10101: led_mode_next = 1'b0;
    5'b10110: led_mode_next = 1'b0;
    5'b10111: led_mode_next = 1'b0; // reset
    5'b11000: led_mode_next = 1'b1;
    5'b11001: led_mode_next = 1'b1;
    5'b11010: led_mode_next = 1'b1;
    5'b11011: led_mode_next = 1'b1;
    5'b11100: led_mode_next = 1'b1;
    5'b11101: led_mode_next = 1'b1;
    5'b11110: led_mode_next = 1'b1;
    5'b11111: led_mode_next = 1'b0; // reset
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    led_mode <= 1'b0;
  end else if(led_mode_en) begin
    led_mode <= led_mode_next;
  end
end
assign write_data_bit = write_data_i[0];

logic  cntr_cmp;
assign cntr_cmp = cntr < 32'd20_000_000;

logic [31:0] cntr_next;
always_comb begin
  case ({cntr_cmp, req, write_enable, soft_reset_addr_cmp, led_mode, soft_reset_write_data_cmp})
    6'b000000: cntr_next = '0;
    6'b000001: cntr_next = '0;
    6'b000010: cntr_next = '0;
    6'b000011: cntr_next = '0;
    6'b000100: cntr_next = '0;
    6'b000101: cntr_next = '0;
    6'b000110: cntr_next = '0;
    6'b000111: cntr_next = '0;
    6'b001000: cntr_next = '0;
    6'b001001: cntr_next = '0;
    6'b001010: cntr_next = '0;
    6'b001011: cntr_next = '0;
    6'b001100: cntr_next = '0;
    6'b001101: cntr_next = '0;
    6'b001110: cntr_next = '0;
    6'b001111: cntr_next = '0;
    6'b010000: cntr_next = '0;
    6'b010001: cntr_next = '0;
    6'b010010: cntr_next = '0;
    6'b010011: cntr_next = '0;
    6'b010100: cntr_next = '0;
    6'b010101: cntr_next = '0;
    6'b010110: cntr_next = '0;
    6'b010111: cntr_next = '0;
    6'b011000: cntr_next = '0;
    6'b011001: cntr_next = '0;
    6'b011010: cntr_next = '0;
    6'b011011: cntr_next = '0;
    6'b011100: cntr_next = '0;
    6'b011101: cntr_next = '0; // reset
    6'b011110: cntr_next = '0;
    6'b011111: cntr_next = '0; // reset

    6'b100000: cntr_next = '0;
    6'b100001: cntr_next = '0;
    6'b100010: cntr_next = cntr + 32'b1;
    6'b100011: cntr_next = cntr + 32'b1;
    6'b100100: cntr_next = '0;
    6'b100101: cntr_next = '0;
    6'b100110: cntr_next = cntr + 32'b1;
    6'b100111: cntr_next = cntr + 32'b1;
    6'b101000: cntr_next = '0;
    6'b101001: cntr_next = '0;
    6'b101010: cntr_next = '0;
    6'b101011: cntr_next = '0;
    6'b101100: cntr_next = '0;
    6'b101101: cntr_next = '0;
    6'b101110: cntr_next = cntr + 32'b1;
    6'b101111: cntr_next = cntr + 32'b1;
    6'b110000: cntr_next = '0;
    6'b110001: cntr_next = '0;
    6'b110010: cntr_next = cntr + 32'b1;
    6'b110011: cntr_next = cntr + 32'b1;
    6'b110100: cntr_next = '0;
    6'b110101: cntr_next = '0;
    6'b110110: cntr_next = cntr + 32'b1;
    6'b110111: cntr_next = cntr + 32'b1;
    6'b111000: cntr_next = '0;
    6'b111001: cntr_next = '0;
    6'b111010: cntr_next = cntr + 32'b1;
    6'b111011: cntr_next = cntr + 32'b1;
    6'b111100: cntr_next = '0;
    6'b111101: cntr_next = '0; // reset
    6'b111110: cntr_next = cntr + 32'b1;
    6'b111111: cntr_next = '0; // reset
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    cntr <= 32'd0;
  end else begin
    cntr <= cntr_next;
  end
end

logic  led_val_addr_cmp;
assign led_val_addr_cmp = addr_i == 32'd0;
logic  write_data_cmp;
assign write_data_cmp = write_data_i[31:16] == 16'd0;

logic led_val_en;
always_comb begin
  case ({req, write_enable, soft_reset_addr_cmp, soft_reset_write_data_cmp, led_val_addr_cmp, write_data_cmp})
    6'b000000: led_val_en = 1'b0;
    6'b000001: led_val_en = 1'b0;
    6'b000010: led_val_en = 1'b0;
    6'b000011: led_val_en = 1'b1;
    6'b000100: led_val_en = 1'b0;
    6'b000101: led_val_en = 1'b0;
    6'b000110: led_val_en = 1'b0;
    6'b000111: led_val_en = 1'b1;
    6'b001000: led_val_en = 1'b0;
    6'b001001: led_val_en = 1'b0;
    6'b001010: led_val_en = 1'b0;
    6'b001011: led_val_en = 1'b1;
    6'b001100: led_val_en = 1'b0;
    6'b001101: led_val_en = 1'b0;
    6'b001110: led_val_en = 1'b0;
    6'b001111: led_val_en = 1'b1;
    6'b010000: led_val_en = 1'b0;
    6'b010001: led_val_en = 1'b0;
    6'b010010: led_val_en = 1'b0;
    6'b010011: led_val_en = 1'b1;
    6'b010100: led_val_en = 1'b0;
    6'b010101: led_val_en = 1'b0;
    6'b010110: led_val_en = 1'b0;
    6'b010111: led_val_en = 1'b1;
    6'b011000: led_val_en = 1'b0;
    6'b011001: led_val_en = 1'b0;
    6'b011010: led_val_en = 1'b0;
    6'b011011: led_val_en = 1'b1;
    6'b011100: led_val_en = 1'b0;
    6'b011101: led_val_en = 1'b0;
    6'b011110: led_val_en = 1'b0;
    6'b011111: led_val_en = 1'b1;
    6'b100000: led_val_en = 1'b0;
    6'b100001: led_val_en = 1'b0;
    6'b100010: led_val_en = 1'b0;
    6'b100011: led_val_en = 1'b1;
    6'b100100: led_val_en = 1'b0;
    6'b100101: led_val_en = 1'b0;
    6'b100110: led_val_en = 1'b0;
    6'b100111: led_val_en = 1'b1;
    6'b101000: led_val_en = 1'b0;
    6'b101001: led_val_en = 1'b0;
    6'b101010: led_val_en = 1'b0;
    6'b101011: led_val_en = 1'b1;
    6'b101100: led_val_en = 1'b0;
    6'b101101: led_val_en = 1'b0;
    6'b101110: led_val_en = 1'b0;
    6'b101111: led_val_en = 1'b1;
    6'b110000: led_val_en = 1'b0;
    6'b110001: led_val_en = 1'b0;
    6'b110010: led_val_en = 1'b0;
    6'b110011: led_val_en = 1'b1;
    6'b110100: led_val_en = 1'b0;
    6'b110101: led_val_en = 1'b0;
    6'b110110: led_val_en = 1'b0;
    6'b110111: led_val_en = 1'b1;
    6'b111000: led_val_en = 1'b0;
    6'b111001: led_val_en = 1'b0;
    6'b111010: led_val_en = 1'b0;
    6'b111011: led_val_en = 1'b1;
    6'b111100: led_val_en = 1'b1; // reset
    6'b111101: led_val_en = 1'b1; // reset
    6'b111110: led_val_en = 1'b1; // reset
    6'b111111: led_val_en = 1'b1; // reset
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    led_val <= 16'd0;
  end
  else if(led_val_en) begin
    led_val <= write_data_i[15:0] & {16{~(req & write_enable & soft_reset_addr_cmp & write_data_bit & soft_reset_write_data_cmp)}};
  end
end

logic  read_data_addr_cmp;
assign read_data_addr_cmp = ~|{addr_i[31:3], addr_i[1:0]};
logic  read_data_addr_bit;
assign read_data_addr_bit = addr_i[2];

logic read_data_en;
always_comb begin
  case ({read_data_addr_bit, req, soft_reset_addr_cmp, write_enable, read_data_addr_cmp, soft_reset_write_data_cmp})
    6'b000000: read_data_en = 1'b0;
    6'b000001: read_data_en = 1'b0;
    6'b000010: read_data_en = 1'b0;
    6'b000011: read_data_en = 1'b0;
    6'b000100: read_data_en = 1'b0;
    6'b000101: read_data_en = 1'b0;
    6'b000110: read_data_en = 1'b0;
    6'b000111: read_data_en = 1'b0;
    6'b001000: read_data_en = 1'b0;
    6'b001001: read_data_en = 1'b0;
    6'b001010: read_data_en = 1'b0;
    6'b001011: read_data_en = 1'b0;
    6'b001100: read_data_en = 1'b0;
    6'b001101: read_data_en = 1'b0;
    6'b001110: read_data_en = 1'b0;
    6'b001111: read_data_en = 1'b0;
    6'b010000: read_data_en = 1'b0;
    6'b010001: read_data_en = 1'b0;
    6'b010010: read_data_en = 1'b1;
    6'b010011: read_data_en = 1'b1;
    6'b010100: read_data_en = 1'b0;
    6'b010101: read_data_en = 1'b0;
    6'b010110: read_data_en = 1'b0;
    6'b010111: read_data_en = 1'b0;
    6'b011000: read_data_en = 1'b0;
    6'b011001: read_data_en = 1'b0;
    6'b011010: read_data_en = 1'b1;
    6'b011011: read_data_en = 1'b1;
    6'b011100: read_data_en = 1'b0;
    6'b011101: read_data_en = 1'b1; // reset
    6'b011110: read_data_en = 1'b0;
    6'b011111: read_data_en = 1'b1; // reset
    6'b100000: read_data_en = 1'b0;
    6'b100001: read_data_en = 1'b0;
    6'b100010: read_data_en = 1'b0;
    6'b100011: read_data_en = 1'b0;
    6'b100100: read_data_en = 1'b0;
    6'b100101: read_data_en = 1'b0;
    6'b100110: read_data_en = 1'b0;
    6'b100111: read_data_en = 1'b0;
    6'b101000: read_data_en = 1'b0;
    6'b101001: read_data_en = 1'b0;
    6'b101010: read_data_en = 1'b0;
    6'b101011: read_data_en = 1'b0;
    6'b101100: read_data_en = 1'b0;
    6'b101101: read_data_en = 1'b0;
    6'b101110: read_data_en = 1'b0;
    6'b101111: read_data_en = 1'b0;
    6'b110000: read_data_en = 1'b0;
    6'b110001: read_data_en = 1'b0;
    6'b110010: read_data_en = 1'b1;
    6'b110011: read_data_en = 1'b1;
    6'b110100: read_data_en = 1'b0;
    6'b110101: read_data_en = 1'b0;
    6'b110110: read_data_en = 1'b0;
    6'b110111: read_data_en = 1'b0;
    6'b111000: read_data_en = 1'b0;
    6'b111001: read_data_en = 1'b0;
    6'b111010: read_data_en = 1'b1;
    6'b111011: read_data_en = 1'b1;
    6'b111100: read_data_en = 1'b0;
    6'b111101: read_data_en = 1'b1; // reset
    6'b111110: read_data_en = 1'b0;
    6'b111111: read_data_en = 1'b1; // reset
  endcase
end

logic [31:0] read_data_next;
always_comb begin
  case ({req, read_data_addr_bit, soft_reset_addr_cmp, write_enable, soft_reset_write_data_cmp})
    5'b00000: read_data_next = read_data_o;
    5'b00001: read_data_next = read_data_o;
    5'b00010: read_data_next = read_data_o;
    5'b00011: read_data_next = read_data_o;
    5'b00100: read_data_next = read_data_o;
    5'b00101: read_data_next = read_data_o;
    5'b00110: read_data_next = read_data_o;
    5'b00111: read_data_next = read_data_o;
    5'b01000: read_data_next = read_data_o;
    5'b01001: read_data_next = read_data_o;
    5'b01010: read_data_next = read_data_o;
    5'b01011: read_data_next = read_data_o;
    5'b01100: read_data_next = read_data_o;
    5'b01101: read_data_next = read_data_o;
    5'b01110: read_data_next = read_data_o;
    5'b01111: read_data_next = read_data_o;
    5'b10000: read_data_next = {16'd0,led_val};
    5'b10001: read_data_next = {16'd0,led_val};
    5'b10010: read_data_next = read_data_o;
    5'b10011: read_data_next = read_data_o;
    5'b10100: read_data_next = {16'd0,led_val};
    5'b10101: read_data_next = {16'd0,led_val};
    5'b10110: read_data_next = read_data_o;
    5'b10111: read_data_next = '0; // reset
    5'b11000: read_data_next = {31'd0,led_mode};
    5'b11001: read_data_next = {31'd0,led_mode};
    5'b11010: read_data_next = read_data_o;
    5'b11011: read_data_next = read_data_o;
    5'b11100: read_data_next = {31'd0,led_mode};
    5'b11101: read_data_next = {31'd0,led_mode};
    5'b11110: read_data_next = read_data_o;
    5'b11111: read_data_next = '0; // reset
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    read_data_o <= 32'd0;
  end
  else if(read_data_en) begin
    read_data_o <= read_data_next;
  end
end

assign soft_reset_addr_cmp = addr_i == 32'h24;
endmodule
