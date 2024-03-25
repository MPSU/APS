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

logic soft_reset;

assign soft_reset = req_i & write_enable_i & (addr_i == 32'h24) & (write_data_i == 1'b1);

assign led_o = cntr < 32'd10_000_000 ? led_val : 32'd0;

logic  addr_cmp;
assign addr_cmp = addr_i == 32'd4;

logic  write_data_cmp;
assign write_data_cmp = write_data_i <= 32'd1;

logic led_mode_en;
always_comb begin
  case ({write_data_cmp, addr_cmp, write_enable_i, soft_reset, req_i})
    5'b00000: led_mode_en = 1'b0;
    5'b00001: led_mode_en = 1'b0;
    5'b00010: led_mode_en = 1'b1;
    5'b00011: led_mode_en = 1'b1;
    5'b00100: led_mode_en = 1'b0;
    5'b00101: led_mode_en = 1'b0;
    5'b00110: led_mode_en = 1'b1;
    5'b00111: led_mode_en = 1'b1;
    5'b01000: led_mode_en = 1'b0;
    5'b01001: led_mode_en = 1'b0;
    5'b01010: led_mode_en = 1'b1;
    5'b01011: led_mode_en = 1'b1;
    5'b01100: led_mode_en = 1'b0;
    5'b01101: led_mode_en = 1'b0;
    5'b01110: led_mode_en = 1'b1;
    5'b01111: led_mode_en = 1'b1;
    5'b10000: led_mode_en = 1'b0;
    5'b10001: led_mode_en = 1'b0;
    5'b10010: led_mode_en = 1'b1;
    5'b10011: led_mode_en = 1'b1;
    5'b10100: led_mode_en = 1'b0;
    5'b10101: led_mode_en = 1'b0;
    5'b10110: led_mode_en = 1'b1;
    5'b10111: led_mode_en = 1'b1;
    5'b11000: led_mode_en = 1'b0;
    5'b11001: led_mode_en = 1'b0;
    5'b11010: led_mode_en = 1'b1;
    5'b11011: led_mode_en = 1'b1;
    5'b11100: led_mode_en = 1'b0;
    5'b11101: led_mode_en = 1'b1;
    5'b11110: led_mode_en = 1'b1;
    5'b11111: led_mode_en = 1'b1;
  endcase
end

logic  led_mode_next;
always_comb begin
  case ({write_data_i[0], soft_reset})
    2'b00: led_mode_next = 1'b0;
    2'b01: led_mode_next = 1'b0;
    2'b10: led_mode_next = 1'b1;
    2'b11: led_mode_next = 1'b0;
  endcase
end

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    led_mode <= 1'b0;
  end else if(led_mode_en) begin
    led_mode <= led_mode_next;
  end
end

always_ff @(posedge clk_i) begin
  if(rst_i | soft_reset) begin
    cntr <= 32'd0;
  end
  else if((cntr < 32'd20_000_000) & led_mode) begin
    cntr <= cntr + 1'b1;
  end
  else begin
    cntr <= 32'd0;
  end
end

always_ff @(posedge clk_i) begin
  if(rst_i | soft_reset) begin
    led_val <= 16'd0;
  end
  else if(req_i & write_enable_i & (addr_i == 32'd0) & (write_data_i[31:16] == 16'd0)) begin
    led_val <= write_data_i[15:0];
  end
  else begin
    led_val <= led_val;
  end
end

always_ff @(posedge clk_i) begin
  if(rst_i | soft_reset) begin
    read_data_o <= 32'd0;
  end
  else if(!req_i | write_enable_i) begin
    read_data_o <= read_data_o;
  end
  else begin
    case(addr_i)
      32'd0: read_data_o <= {16'd0,led_val};
      32'd4: read_data_o <= {31'd0,led_mode};
      default: read_data_o <= read_data_o;
    endcase
  end
end

endmodule
