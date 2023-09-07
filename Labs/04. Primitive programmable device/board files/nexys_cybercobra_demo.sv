`timescale 1ns / 1ps

module nexys_CYBERcobra(
    input CLK100,
    input resetn,
    input BTND,
    input [15:0] SW,
    output CA, CB, CC, CD, CE, CF, CG, 
    output [7:0] AN
    );
    
    CYBERcobra dut(
    .clk_i(CLK100),
    .rst_i(!resetn),
    .sw_i({7'b0,splash,SW[7:0]}),
    .out_o(out)
    );

localparam pwm = 1000;
reg [9:0] counter;
reg [3:0] semseg;
reg [7:0] ANreg;
reg CAr, CBr, CCr, CDr, CEr, CFr, CGr;
reg [3:0] btn;
reg [10:0] btn_reg;
wire splash;
wire [31:0] out;

assign AN[7:0] = ANreg[7:0];
assign {CA, CB, CC, CD, CE, CF, CG} = {CAr, CBr, CCr, CDr, CEr, CFr, CGr};
assign splash = ((btn == 4'b1111) ^ btn_reg[10]) && (btn == 4'b1111);

always @(posedge CLK100) begin
    if (!resetn) begin
        counter <= 'b0;
        ANreg[7:0] <= 8'b11111111;
        {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111;
        btn <= 4'b0;
        btn_reg <= 0;
    end 
    else begin
        btn <= (btn << 1'b1) + BTND;
        btn_reg <= (btn_reg << 1'b1) + (btn == 4'b1111);
        if (counter < pwm) counter = counter + 'b1;
        else begin
            counter = 'b0;
            ANreg[1] <= ANreg[0];
            ANreg[2] <= ANreg[1];
            ANreg[3] <= ANreg[2];
            ANreg[4] <= ANreg[3];
            ANreg[5] <= ANreg[4];
            ANreg[6] <= ANreg[5];
            ANreg[7] <= ANreg[6];
            ANreg[0] <= !(ANreg[6:0] == 7'b1111111);
        end
        case (1'b0)
            ANreg[0]: semseg <= out[3 : 0];
            ANreg[1]: semseg <= out[7 : 4];
            ANreg[2]: semseg <= out[11: 8];
            ANreg[3]: semseg <= out[15:12];
            ANreg[4]: semseg <= out[19:16];
            ANreg[5]: semseg <= out[23:20];
            ANreg[6]: semseg <= out[27:24];
            ANreg[7]: semseg <= out[31:28];
        endcase
        case (semseg)
            4'h1: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //L
            4'h3: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0110110; //?
            4'h8: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000001; //O
            4'hA: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001000; //A
            4'hC: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1001000; //H
         default: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111; //
        endcase
     end
  end

endmodule
