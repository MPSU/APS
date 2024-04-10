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

logic [31:0]  G0jy;

logic  szgbhtISZO6lWdZ0zBq;

logic  GHJMElpRUEQEEP7EcBqK9y7Np;
assign GHJMElpRUEQEEP7EcBqK9y7Np = write_data_i == 1'b1;

assign led_o = G0jy < 32'd10_000_000 ? led_val : 32'd0;

logic  h9z1ckclZaHUmRYYk;
logic  E8on91LjAMIk;
assign h9z1ckclZaHUmRYYk = addr_i == (32'h146 ^ 32'd322);

localparam bit [31:0] tamX10PbxPLym4NQXMpBFA1ZPCMfu = 32'o6236621706 + 32'h643c9869 + 32'o14614644163 + 32'o16454156121 + 32'h19495cff + 32'h2ae8944a + 32'h625558ec + 32'o4343417451 + 32'o10672076315 + 32'o7506654272 + 32'o12037553653 + 32'h2eb141f2 + 32'h41b71efb + 32'h79e2a9e3 + 32'o16521360506 + 32'o12127600174 + 32'o13364061302 + 32'h12200854 + 32'o11554223770 + 32'h833a88de;

logic  d2Vdz1otfNKET9pkgF4b2ur;
assign E8on91LjAMIk = write_enable_i;
assign d2Vdz1otfNKET9pkgF4b2ur = write_data_i <= tamX10PbxPLym4NQXMpBFA1ZPCMfu;

logic  X9e;
assign X9e = req_i;
logic  YaRCbt0zk9bDlW;

logic kd21aSJpdPn;
always_comb begin
  case ({szgbhtISZO6lWdZ0zBq, d2Vdz1otfNKET9pkgF4b2ur, h9z1ckclZaHUmRYYk, E8on91LjAMIk, X9e, GHJMElpRUEQEEP7EcBqK9y7Np})
    6'b000000: kd21aSJpdPn = 1'b0;
    6'b000001: kd21aSJpdPn = 1'b0;
    6'b000010: kd21aSJpdPn = 1'b0;
    6'b000011: kd21aSJpdPn = 1'b0;
    6'b000100: kd21aSJpdPn = 1'b0;
    6'b000101: kd21aSJpdPn = 1'b0;
    6'b000110: kd21aSJpdPn = 1'b0;
    6'b000111: kd21aSJpdPn = 1'b0;
    6'b001000: kd21aSJpdPn = 1'b0;
    6'b001001: kd21aSJpdPn = 1'b0;
    6'b001010: kd21aSJpdPn = 1'b0;
    6'b001011: kd21aSJpdPn = 1'b0;
    6'b001100: kd21aSJpdPn = 1'b0;
    6'b001101: kd21aSJpdPn = 1'b0;
    6'b001110: kd21aSJpdPn = 1'b0;
    6'b001111: kd21aSJpdPn = 1'b0;
    6'b010000: kd21aSJpdPn = 1'b0;
    6'b010001: kd21aSJpdPn = 1'b0;
    6'b010010: kd21aSJpdPn = 1'b0;
    6'b010011: kd21aSJpdPn = 1'b0;
    6'b010100: kd21aSJpdPn = 1'b0;
    6'b010101: kd21aSJpdPn = 1'b0;
    6'b010110: kd21aSJpdPn = 1'b0;
    6'b010111: kd21aSJpdPn = 1'b0;
    6'b011000: kd21aSJpdPn = 1'b0;
    6'b011001: kd21aSJpdPn = 1'b0;
    6'b011010: kd21aSJpdPn = 1'b0;
    6'b011011: kd21aSJpdPn = 1'b0;
    6'b011100: kd21aSJpdPn = 1'b0;
    6'b011101: kd21aSJpdPn = 1'b0;
    6'b011110: kd21aSJpdPn = 1'b1;
    6'b011111: kd21aSJpdPn = 1'b1;
    6'b100000: kd21aSJpdPn = 1'b0;
    6'b100001: kd21aSJpdPn = 1'b0;
    6'b100010: kd21aSJpdPn = 1'b0;
    6'b100011: kd21aSJpdPn = 1'b0;
    6'b100100: kd21aSJpdPn = 1'b0;
    6'b100101: kd21aSJpdPn = 1'b0;
    6'b100110: kd21aSJpdPn = 1'b0;
    6'b100111: kd21aSJpdPn = 1'b1;
    6'b101000: kd21aSJpdPn = 1'b0;
    6'b101001: kd21aSJpdPn = 1'b0;
    6'b101010: kd21aSJpdPn = 1'b0;
    6'b101011: kd21aSJpdPn = 1'b0;
    6'b101100: kd21aSJpdPn = 1'b0;
    6'b101101: kd21aSJpdPn = 1'b0;
    6'b101110: kd21aSJpdPn = 1'b0;
    6'b101111: kd21aSJpdPn = 1'b1;
    6'b110000: kd21aSJpdPn = 1'b0;
    6'b110001: kd21aSJpdPn = 1'b0;
    6'b110010: kd21aSJpdPn = 1'b0;
    6'b110011: kd21aSJpdPn = 1'b0;
    6'b110100: kd21aSJpdPn = 1'b0;
    6'b110101: kd21aSJpdPn = 1'b0;
    6'b110110: kd21aSJpdPn = 1'b0;
    6'b110111: kd21aSJpdPn = 1'b1;
    6'b111000: kd21aSJpdPn = 1'b0;
    6'b111001: kd21aSJpdPn = 1'b0;
    6'b111010: kd21aSJpdPn = 1'b0;
    6'b111011: kd21aSJpdPn = 1'b0;
    6'b111100: kd21aSJpdPn = 1'b0;
    6'b111101: kd21aSJpdPn = 1'b0;
    6'b111110: kd21aSJpdPn = 1'b1;
    6'b111111: kd21aSJpdPn = 1'b1;
  endcase
end

logic  JUTUkxXfzZHi0;
always_comb begin
  case ({X9e, YaRCbt0zk9bDlW, E8on91LjAMIk, szgbhtISZO6lWdZ0zBq, GHJMElpRUEQEEP7EcBqK9y7Np})
    5'b00000: JUTUkxXfzZHi0 = 1'b0;
    5'b00001: JUTUkxXfzZHi0 = 1'b0;
    5'b00010: JUTUkxXfzZHi0 = 1'b0;
    5'b00011: JUTUkxXfzZHi0 = 1'b0;
    5'b00100: JUTUkxXfzZHi0 = 1'b0;
    5'b00101: JUTUkxXfzZHi0 = 1'b0;
    5'b00110: JUTUkxXfzZHi0 = 1'b0;
    5'b00111: JUTUkxXfzZHi0 = 1'b0;
    5'b01000: JUTUkxXfzZHi0 = 1'b1;
    5'b01001: JUTUkxXfzZHi0 = 1'b1;
    5'b01010: JUTUkxXfzZHi0 = 1'b1;
    5'b01011: JUTUkxXfzZHi0 = 1'b1;
    5'b01100: JUTUkxXfzZHi0 = 1'b1;
    5'b01101: JUTUkxXfzZHi0 = 1'b1;
    5'b01110: JUTUkxXfzZHi0 = 1'b1;
    5'b01111: JUTUkxXfzZHi0 = 1'b1;
    5'b10000: JUTUkxXfzZHi0 = 1'b0;
    5'b10001: JUTUkxXfzZHi0 = 1'b0;
    5'b10010: JUTUkxXfzZHi0 = 1'b0;
    5'b10011: JUTUkxXfzZHi0 = 1'b0;
    5'b10100: JUTUkxXfzZHi0 = 1'b0;
    5'b10101: JUTUkxXfzZHi0 = 1'b0;
    5'b10110: JUTUkxXfzZHi0 = 1'b0;
    5'b10111: JUTUkxXfzZHi0 = 1'b0;
    5'b11000: JUTUkxXfzZHi0 = 1'b1;
    5'b11001: JUTUkxXfzZHi0 = 1'b1;
    5'b11010: JUTUkxXfzZHi0 = 1'b1;
    5'b11011: JUTUkxXfzZHi0 = 1'b1;
    5'b11100: JUTUkxXfzZHi0 = 1'b1;
    5'b11101: JUTUkxXfzZHi0 = 1'b1;
    5'b11110: JUTUkxXfzZHi0 = 1'b1;
    5'b11111: JUTUkxXfzZHi0 = 1'b0;
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    led_mode <= 1'b0;
  end else if(kd21aSJpdPn) begin
    led_mode <= JUTUkxXfzZHi0;
  end
end
assign YaRCbt0zk9bDlW = write_data_i[0];

logic  aNirtmfc;
assign aNirtmfc = G0jy < 32'd20_000_000;

logic [31:0] mTwefHrES;
always_comb begin
  case ({aNirtmfc, X9e, E8on91LjAMIk, szgbhtISZO6lWdZ0zBq, led_mode, GHJMElpRUEQEEP7EcBqK9y7Np})
    6'b000000: mTwefHrES = '0;
    6'b000001: mTwefHrES = '0;
    6'b000010: mTwefHrES = '0;
    6'b000011: mTwefHrES = '0;
    6'b000100: mTwefHrES = '0;
    6'b000101: mTwefHrES = '0;
    6'b000110: mTwefHrES = '0;
    6'b000111: mTwefHrES = '0;
    6'b001000: mTwefHrES = '0;
    6'b001001: mTwefHrES = '0;
    6'b001010: mTwefHrES = '0;
    6'b001011: mTwefHrES = '0;
    6'b001100: mTwefHrES = '0;
    6'b001101: mTwefHrES = '0;
    6'b001110: mTwefHrES = '0;
    6'b001111: mTwefHrES = '0;
    6'b010000: mTwefHrES = '0;
    6'b010001: mTwefHrES = '0;
    6'b010010: mTwefHrES = '0;
    6'b010011: mTwefHrES = '0;
    6'b010100: mTwefHrES = '0;
    6'b010101: mTwefHrES = '0;
    6'b010110: mTwefHrES = '0;
    6'b010111: mTwefHrES = '0;
    6'b011000: mTwefHrES = '0;
    6'b011001: mTwefHrES = '0;
    6'b011010: mTwefHrES = '0;
    6'b011011: mTwefHrES = '0;
    6'b011100: mTwefHrES = '0;
    6'b011101: mTwefHrES = '0;
    6'b011110: mTwefHrES = '0;
    6'b011111: mTwefHrES = '0;

    6'b100000: mTwefHrES = '0;
    6'b100001: mTwefHrES = '0;
    6'b100010: mTwefHrES = G0jy + 32'b1;
    6'b100011: mTwefHrES = G0jy + 32'b1;
    6'b100100: mTwefHrES = '0;
    6'b100101: mTwefHrES = '0;
    6'b100110: mTwefHrES = G0jy + 32'b1;
    6'b100111: mTwefHrES = G0jy + 32'b1;
    6'b101000: mTwefHrES = '0;
    6'b101001: mTwefHrES = '0;
    6'b101010: mTwefHrES = '0;
    6'b101011: mTwefHrES = '0;
    6'b101100: mTwefHrES = '0;
    6'b101101: mTwefHrES = '0;
    6'b101110: mTwefHrES = G0jy + 32'b1;
    6'b101111: mTwefHrES = G0jy + 32'b1;
    6'b110000: mTwefHrES = '0;
    6'b110001: mTwefHrES = '0;
    6'b110010: mTwefHrES = G0jy + 32'b1;
    6'b110011: mTwefHrES = G0jy + 32'b1;
    6'b110100: mTwefHrES = '0;
    6'b110101: mTwefHrES = '0;
    6'b110110: mTwefHrES = G0jy + 32'b1;
    6'b110111: mTwefHrES = G0jy + 32'b1;
    6'b111000: mTwefHrES = '0;
    6'b111001: mTwefHrES = '0;
    6'b111010: mTwefHrES = G0jy + 32'b1;
    6'b111011: mTwefHrES = G0jy + 32'b1;
    6'b111100: mTwefHrES = '0;
    6'b111101: mTwefHrES = '0;
    6'b111110: mTwefHrES = G0jy + 32'b1;
    6'b111111: mTwefHrES = '0;
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    G0jy <= 32'd0;
  end else begin
    G0jy <= mTwefHrES;
  end
end

logic  u8n925jRHw6yY2OA;
assign u8n925jRHw6yY2OA = addr_i == 32'd0;
logic  Sksa8hJRDqKf6y;
assign Sksa8hJRDqKf6y = write_data_i[31:16] == 16'd0;

logic kq8KzeiLOE;
always_comb begin
  case ({X9e, E8on91LjAMIk, szgbhtISZO6lWdZ0zBq, GHJMElpRUEQEEP7EcBqK9y7Np, u8n925jRHw6yY2OA, Sksa8hJRDqKf6y})
    6'b000000: kq8KzeiLOE = 1'b0;
    6'b000001: kq8KzeiLOE = 1'b0;
    6'b000010: kq8KzeiLOE = 1'b0;
    6'b000011: kq8KzeiLOE = 1'b1;
    6'b000100: kq8KzeiLOE = 1'b0;
    6'b000101: kq8KzeiLOE = 1'b0;
    6'b000110: kq8KzeiLOE = 1'b0;
    6'b000111: kq8KzeiLOE = 1'b1;
    6'b001000: kq8KzeiLOE = 1'b0;
    6'b001001: kq8KzeiLOE = 1'b0;
    6'b001010: kq8KzeiLOE = 1'b0;
    6'b001011: kq8KzeiLOE = 1'b1;
    6'b001100: kq8KzeiLOE = 1'b0;
    6'b001101: kq8KzeiLOE = 1'b0;
    6'b001110: kq8KzeiLOE = 1'b0;
    6'b001111: kq8KzeiLOE = 1'b1;
    6'b010000: kq8KzeiLOE = 1'b0;
    6'b010001: kq8KzeiLOE = 1'b0;
    6'b010010: kq8KzeiLOE = 1'b0;
    6'b010011: kq8KzeiLOE = 1'b1;
    6'b010100: kq8KzeiLOE = 1'b0;
    6'b010101: kq8KzeiLOE = 1'b0;
    6'b010110: kq8KzeiLOE = 1'b0;
    6'b010111: kq8KzeiLOE = 1'b1;
    6'b011000: kq8KzeiLOE = 1'b0;
    6'b011001: kq8KzeiLOE = 1'b0;
    6'b011010: kq8KzeiLOE = 1'b0;
    6'b011011: kq8KzeiLOE = 1'b1;
    6'b011100: kq8KzeiLOE = 1'b0;
    6'b011101: kq8KzeiLOE = 1'b0;
    6'b011110: kq8KzeiLOE = 1'b0;
    6'b011111: kq8KzeiLOE = 1'b1;
    6'b100000: kq8KzeiLOE = 1'b0;
    6'b100001: kq8KzeiLOE = 1'b0;
    6'b100010: kq8KzeiLOE = 1'b0;
    6'b100011: kq8KzeiLOE = 1'b1;
    6'b100100: kq8KzeiLOE = 1'b0;
    6'b100101: kq8KzeiLOE = 1'b0;
    6'b100110: kq8KzeiLOE = 1'b0;
    6'b100111: kq8KzeiLOE = 1'b1;
    6'b101000: kq8KzeiLOE = 1'b0;
    6'b101001: kq8KzeiLOE = 1'b0;
    6'b101010: kq8KzeiLOE = 1'b0;
    6'b101011: kq8KzeiLOE = 1'b1;
    6'b101100: kq8KzeiLOE = 1'b0;
    6'b101101: kq8KzeiLOE = 1'b0;
    6'b101110: kq8KzeiLOE = 1'b0;
    6'b101111: kq8KzeiLOE = 1'b1;
    6'b110000: kq8KzeiLOE = 1'b0;
    6'b110001: kq8KzeiLOE = 1'b0;
    6'b110010: kq8KzeiLOE = 1'b0;
    6'b110011: kq8KzeiLOE = 1'b1;
    6'b110100: kq8KzeiLOE = 1'b0;
    6'b110101: kq8KzeiLOE = 1'b0;
    6'b110110: kq8KzeiLOE = 1'b0;
    6'b110111: kq8KzeiLOE = 1'b1;
    6'b111000: kq8KzeiLOE = 1'b0;
    6'b111001: kq8KzeiLOE = 1'b0;
    6'b111010: kq8KzeiLOE = 1'b0;
    6'b111011: kq8KzeiLOE = 1'b1;
    6'b111100: kq8KzeiLOE = 1'b1;
    6'b111101: kq8KzeiLOE = 1'b1;
    6'b111110: kq8KzeiLOE = 1'b1;
    6'b111111: kq8KzeiLOE = 1'b1;
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    led_val <= 16'd0;
  end
  else if(kq8KzeiLOE) begin
    led_val <= write_data_i[15:0] & {16{~(X9e & E8on91LjAMIk & szgbhtISZO6lWdZ0zBq & YaRCbt0zk9bDlW & GHJMElpRUEQEEP7EcBqK9y7Np)}};
  end
end

logic  tECGZrHGXNZHv7hEFV;
assign tECGZrHGXNZHv7hEFV = ~|{addr_i[31:3], addr_i[1:0]};
logic  YBnE7pVdlTe8g7B8Mh;
assign YBnE7pVdlTe8g7B8Mh = addr_i[2];

logic Sw0wQLq1pYY7;
always_comb begin
  case ({YBnE7pVdlTe8g7B8Mh, X9e, szgbhtISZO6lWdZ0zBq, E8on91LjAMIk, tECGZrHGXNZHv7hEFV, GHJMElpRUEQEEP7EcBqK9y7Np})
    6'b000000: Sw0wQLq1pYY7 = 1'b0;
    6'b000001: Sw0wQLq1pYY7 = 1'b0;
    6'b000010: Sw0wQLq1pYY7 = 1'b0;
    6'b000011: Sw0wQLq1pYY7 = 1'b0;
    6'b000100: Sw0wQLq1pYY7 = 1'b0;
    6'b000101: Sw0wQLq1pYY7 = 1'b0;
    6'b000110: Sw0wQLq1pYY7 = 1'b0;
    6'b000111: Sw0wQLq1pYY7 = 1'b0;
    6'b001000: Sw0wQLq1pYY7 = 1'b0;
    6'b001001: Sw0wQLq1pYY7 = 1'b0;
    6'b001010: Sw0wQLq1pYY7 = 1'b0;
    6'b001011: Sw0wQLq1pYY7 = 1'b0;
    6'b001100: Sw0wQLq1pYY7 = 1'b0;
    6'b001101: Sw0wQLq1pYY7 = 1'b0;
    6'b001110: Sw0wQLq1pYY7 = 1'b0;
    6'b001111: Sw0wQLq1pYY7 = 1'b0;
    6'b010000: Sw0wQLq1pYY7 = 1'b0;
    6'b010001: Sw0wQLq1pYY7 = 1'b0;
    6'b010010: Sw0wQLq1pYY7 = 1'b1;
    6'b010011: Sw0wQLq1pYY7 = 1'b1;
    6'b010100: Sw0wQLq1pYY7 = 1'b0;
    6'b010101: Sw0wQLq1pYY7 = 1'b0;
    6'b010110: Sw0wQLq1pYY7 = 1'b0;
    6'b010111: Sw0wQLq1pYY7 = 1'b0;
    6'b011000: Sw0wQLq1pYY7 = 1'b0;
    6'b011001: Sw0wQLq1pYY7 = 1'b0;
    6'b011010: Sw0wQLq1pYY7 = 1'b1;
    6'b011011: Sw0wQLq1pYY7 = 1'b1;
    6'b011100: Sw0wQLq1pYY7 = 1'b0;
    6'b011101: Sw0wQLq1pYY7 = 1'b1;
    6'b011110: Sw0wQLq1pYY7 = 1'b0;
    6'b011111: Sw0wQLq1pYY7 = 1'b1;
    6'b100000: Sw0wQLq1pYY7 = 1'b0;
    6'b100001: Sw0wQLq1pYY7 = 1'b0;
    6'b100010: Sw0wQLq1pYY7 = 1'b0;
    6'b100011: Sw0wQLq1pYY7 = 1'b0;
    6'b100100: Sw0wQLq1pYY7 = 1'b0;
    6'b100101: Sw0wQLq1pYY7 = 1'b0;
    6'b100110: Sw0wQLq1pYY7 = 1'b0;
    6'b100111: Sw0wQLq1pYY7 = 1'b0;
    6'b101000: Sw0wQLq1pYY7 = 1'b0;
    6'b101001: Sw0wQLq1pYY7 = 1'b0;
    6'b101010: Sw0wQLq1pYY7 = 1'b0;
    6'b101011: Sw0wQLq1pYY7 = 1'b0;
    6'b101100: Sw0wQLq1pYY7 = 1'b0;
    6'b101101: Sw0wQLq1pYY7 = 1'b0;
    6'b101110: Sw0wQLq1pYY7 = 1'b0;
    6'b101111: Sw0wQLq1pYY7 = 1'b0;
    6'b110000: Sw0wQLq1pYY7 = 1'b0;
    6'b110001: Sw0wQLq1pYY7 = 1'b0;
    6'b110010: Sw0wQLq1pYY7 = 1'b1;
    6'b110011: Sw0wQLq1pYY7 = 1'b1;
    6'b110100: Sw0wQLq1pYY7 = 1'b0;
    6'b110101: Sw0wQLq1pYY7 = 1'b0;
    6'b110110: Sw0wQLq1pYY7 = 1'b0;
    6'b110111: Sw0wQLq1pYY7 = 1'b0;
    6'b111000: Sw0wQLq1pYY7 = 1'b0;
    6'b111001: Sw0wQLq1pYY7 = 1'b0;
    6'b111010: Sw0wQLq1pYY7 = 1'b1;
    6'b111011: Sw0wQLq1pYY7 = 1'b1;
    6'b111100: Sw0wQLq1pYY7 = 1'b0;
    6'b111101: Sw0wQLq1pYY7 = 1'b1;
    6'b111110: Sw0wQLq1pYY7 = 1'b0;
    6'b111111: Sw0wQLq1pYY7 = 1'b1;
  endcase
end

logic [31:0] ZuHZYJEOvjcYVi;
always_comb begin
  case ({X9e, YBnE7pVdlTe8g7B8Mh, szgbhtISZO6lWdZ0zBq, E8on91LjAMIk, GHJMElpRUEQEEP7EcBqK9y7Np})
    5'b00000: ZuHZYJEOvjcYVi = read_data_o;
    5'b00001: ZuHZYJEOvjcYVi = read_data_o;
    5'b00010: ZuHZYJEOvjcYVi = read_data_o;
    5'b00011: ZuHZYJEOvjcYVi = read_data_o;
    5'b00100: ZuHZYJEOvjcYVi = read_data_o;
    5'b00101: ZuHZYJEOvjcYVi = read_data_o;
    5'b00110: ZuHZYJEOvjcYVi = read_data_o;
    5'b00111: ZuHZYJEOvjcYVi = read_data_o;
    5'b01000: ZuHZYJEOvjcYVi = read_data_o;
    5'b01001: ZuHZYJEOvjcYVi = read_data_o;
    5'b01010: ZuHZYJEOvjcYVi = read_data_o;
    5'b01011: ZuHZYJEOvjcYVi = read_data_o;
    5'b01100: ZuHZYJEOvjcYVi = read_data_o;
    5'b01101: ZuHZYJEOvjcYVi = read_data_o;
    5'b01110: ZuHZYJEOvjcYVi = read_data_o;
    5'b01111: ZuHZYJEOvjcYVi = read_data_o;
    5'b10000: ZuHZYJEOvjcYVi = {16'd0,led_val};
    5'b10001: ZuHZYJEOvjcYVi = {16'd0,led_val};
    5'b10010: ZuHZYJEOvjcYVi = read_data_o;
    5'b10011: ZuHZYJEOvjcYVi = read_data_o;
    5'b10100: ZuHZYJEOvjcYVi = {16'd0,led_val};
    5'b10101: ZuHZYJEOvjcYVi = {16'd0,led_val};
    5'b10110: ZuHZYJEOvjcYVi = read_data_o;
    5'b10111: ZuHZYJEOvjcYVi = '0;
    5'b11000: ZuHZYJEOvjcYVi = {31'd0,led_mode};
    5'b11001: ZuHZYJEOvjcYVi = {31'd0,led_mode};
    5'b11010: ZuHZYJEOvjcYVi = read_data_o;
    5'b11011: ZuHZYJEOvjcYVi = read_data_o;
    5'b11100: ZuHZYJEOvjcYVi = {31'd0,led_mode};
    5'b11101: ZuHZYJEOvjcYVi = {31'd0,led_mode};
    5'b11110: ZuHZYJEOvjcYVi = read_data_o;
    5'b11111: ZuHZYJEOvjcYVi = '0;
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    read_data_o <= 32'd0;
  end
  else if(Sw0wQLq1pYY7) begin
    read_data_o <= ZuHZYJEOvjcYVi;
  end
end

assign szgbhtISZO6lWdZ0zBq = addr_i == 32'h24;
endmodule
