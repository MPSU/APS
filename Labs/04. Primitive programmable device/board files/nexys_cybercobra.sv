`timescale 1ns / 1ps

module nexys_CYBERcobra_dz(
    input CLK100,
    input resetn,
    input BTND,
    input  [15:0] SW,
    output CA, CB, CC, CD, CE, CF, CG, 
    output [7:0] AN
    );
    
    CYBERcobra dut(
    .clk_i(btn),
    .rst_i(!resetn),
    .sw_i(SW[15:0]),
    .out_o(out)
    );

localparam pwm = 1000;
reg [9:0] counter;
reg [3:0] semseg;
reg [7:0] ANreg;
reg CAr, CBr, CCr, CDr, CEr, CFr, CGr;
reg btn;
wire [31:0] out;

assign AN[7:0] = ANreg[7:0];
assign {CA, CB, CC, CD, CE, CF, CG} = {CAr, CBr, CCr, CDr, CEr, CFr, CGr};


always @(posedge CLK100) begin
    if (!resetn) begin
        counter <= 'b0;
        ANreg[7:0] <= 8'b11111111;
        {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111;
        btn <= BTND;
    end
    else begin
        btn <= BTND;
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
            4'h0: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000001;
            4'h1: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1001111;
            4'h2: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0010010;
            4'h3: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000110;
            4'h4: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1001100;
            4'h5: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0100100;
            4'h6: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0100000;
            4'h7: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001111;
            4'h8: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000000;
            4'h9: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000100;
            4'hA: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001000;
            4'hB: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1100000;
            4'hC: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0110001;
            4'hD: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1000010;
            4'hE: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0110000;
            4'hF: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0111000;
            default: {CAr,CBr,CCr,CDr, CEr, CFr, CGr} <= 7'b0111111;
        endcase
     end
  end

endmodule
