module PS2Receiver(
  input  logic        clk,
  input  logic        kclk,
  input  logic        kdata,
  output logic [15:0] keycodeout,
  output              keycode_valid
  );

  logic       flag;
  logic [3:0] flag_shift;
  logic       kclkf, kdataf;
  logic [3:0] cnt;

  assign keycode_valid = flag_shift[0] && !flag_shift[2];

  initial begin //for tb
    cnt = 0;
    keycodeout = 0;
    flag_shift = 0;
    flag = 0;
  end

debouncer debounce(
  .clk(clk),
  .I0(kclk),
  .I1(kdata),
  .O0(kclkf),
  .O1(kdataf)
);
always@(posedge clk) begin
  flag_shift <= (flag_shift << 1) + flag;
end

always_ff @(negedge(kclkf))begin
  case(cnt)
    0:if(keycodeout != 16'hE000)keycodeout <= 0;//Start bit
    1:keycodeout[0]<=kdataf;
    2:keycodeout[1]<=kdataf;
    3:keycodeout[2]<=kdataf;
    4:keycodeout[3]<=kdataf;
    5:keycodeout[4]<=kdataf;
    6:keycodeout[5]<=kdataf;
    7:keycodeout[6]<=kdataf;
    8:keycodeout[7]<=kdataf;
    //TODO ADD PARITY CHECK
    9:begin
      flag<=1'b1;
      if(keycodeout[7:0] == 8'hE0) begin
        keycodeout <= {keycodeout[7:0], 8'd0};
      end
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
  logi Iv0=0,Iv1=0;
  logi out0, out1;

  always_ff @(posedge(clk))begin
    if (I0==Iv0) begin
      if (cnt0==19)O0<=I0;
      else cnt0<=cnt0+1;
    end
    else begin
      cnt0<="00000";
      Iv0<=I0;
    end
    if (I1==Iv1)begin
      if (cnt1==19)O1<=I1;
      else cnt1<=cnt1+1;
    end
    else begin
      cnt1<="00000";
      Iv1<=I1;
    end
  end

endmodule
