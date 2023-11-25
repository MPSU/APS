module PS2Receiver(
  input  logic        clk_i,
  input  logic        kclk_i,
  input  logic        kdata_i,
  output logic [7:0]  keycodeout_o,
  output              keycode_valid_o
  );

  logic       flag;
  logic [3:0] flag_shift;
  logic       kclkf, kdataf;
  logic [3:0] cnt;

  assign keycode_valid_o = flag_shift[0] && !flag_shift[2];

  initial begin //for tb
    cnt = 0;
    keycodeout_o = 0;
    flag_shift = 0;
    flag = 0;
  end

debouncer debounce(
  .clk(clk_i),
  .I0(kclk_i),
  .I1(kdata_i),
  .O0(kclkf),
  .O1(kdataf)
);
always@(posedge clk_i) begin
  flag_shift <= (flag_shift << 1) + flag;
end

always_ff @(negedge(kclkf))begin
  case(cnt)
    0:;
    1:keycodeout_o[0]<=kdataf;
    2:keycodeout_o[1]<=kdataf;
    3:keycodeout_o[2]<=kdataf;
    4:keycodeout_o[3]<=kdataf;
    5:keycodeout_o[4]<=kdataf;
    6:keycodeout_o[5]<=kdataf;
    7:keycodeout_o[6]<=kdataf;
    8:keycodeout_o[7]<=kdataf;
    //TODO ADD PARITY CHECK
    9:begin
      flag<=1'b1;
    end
    10:flag<=1'b0;
    default: cnt <= 0;
  endcase
  if(cnt<=9) cnt<=cnt+1;
  else if(cnt==10) cnt<=0;
end

endmodule


module debouncer(
  input  logic clk,
  input  logic I0,
  input  logic I1,
  output logic O0,
  output logic O1
    );

  logic [4:0]cnt0, cnt1;
  logic Iv0=0,Iv1=0;
  logic out0, out1;

  always_ff @(posedge(clk))begin
    if (I0==Iv0) begin
      if (cnt0==19)O0<=I0;
      else cnt0<=cnt0+1;
    end
    else begin
      cnt0<=5'd0;
      Iv0<=I0;
    end
    if (I1==Iv1)begin
      if (cnt1==19)O1<=I1;
      else cnt1<=cnt1+1;
    end
    else begin
      cnt1<=5'd0;
      Iv1<=I1;
    end
  end

endmodule
