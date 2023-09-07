`timescale 1ns / 1ps

module nexys_alu(
    input CLK100,
    input resetn,
    input  [15:0] SW,
    output [15:0] LED,
    output CA, CB, CC, CD, CE, CF, CG,
    output [7:0] AN
    );
import alu_opcodes_pkg::*;
wire [4:0]               operator_i;
wire [31:0]              operand_a_i;
wire [31:0]              operand_b_i;

wire [31:0]              result_o;
wire                     comparison_result_o;

localparam pwm = 1000;
reg [9:0] counter;
reg [3:0] semseg;
reg [7:0] ANreg;
reg CAr, CBr, CCr, CDr, CEr, CFr, CGr;
reg [15:0] LEDr;
reg minus;

alu_riscv DUT
(
  .ALUOp  (operator_i),
  .A      (operand_a_i),
  .B      (operand_b_i),

  .Result (result_o),
  .Flag   (comparison_result_o)
);

assign operator_i  = SW[4:0];
assign operand_b_i = {{28{SW[10]}},SW[9:6]};
assign operand_a_i = {{28{SW[15]}},SW[14:11]};

assign LED[15:0] = LEDr[15:0];

assign AN[7:0] = ANreg[7:0];
assign {CA, CB, CC, CD, CE, CF, CG} = {CAr, CBr, CCr, CDr, CEr, CFr, CGr};

initial ANreg[7:0] = 8'b11111110;

always @(posedge CLK100) begin
    if (!resetn) begin
        LEDr[15:0] <= 'b0;
        counter <= 'b0;
        ANreg[7:0] <= 8'b11111111;
        {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111;
    end 
    else begin
        LEDr[14:0] <= result_o[14:0];
        LEDr[15] <= comparison_result_o;
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
            ANreg[0] <= !(SW[5] && (ANreg[6:0] == 7'b1111111));
        end
        case (1'b0)
            ANreg[0]: semseg <= result_o[31] ? ( ~result_o + 1          ) % 4'd10: (result_o         ) % 4'd10;
            ANreg[1]: semseg <= result_o[31] ? ((~result_o + 1) / 'd10  ) % 4'd10: (result_o / 'd10  ) % 4'd10;
            ANreg[2]: semseg <= result_o[31] ? ((~result_o + 1) / 'd100 ) % 4'd10: (result_o / 'd100 ) % 4'd10;
            ANreg[3]: semseg <= result_o[31] ? ((~result_o + 1) / 'd1000) % 4'd10: (result_o / 'd1000) % 4'd10;
            ANreg[4]: semseg <= operand_b_i[31] ? ( ~operand_b_i + 1        ) % 4'd10: (operand_b_i       ) % 4'd10;
            ANreg[5]: semseg <= operand_b_i[31] ? ((~operand_b_i + 1) / 'd10) % 4'd10: (operand_b_i / 'd10) % 4'd10;
            ANreg[6]: semseg <= operand_a_i[31] ? ( ~operand_a_i + 1        ) % 4'd10: (operand_a_i       ) % 4'd10;
            ANreg[7]: semseg <= operand_a_i[31] ? ((~operand_a_i + 1) / 'd10) % 4'd10: (operand_a_i / 'd10) % 4'd10;
        endcase
        minus <= (operator_i == ALU_ADD || operator_i == ALU_SUB || operator_i == ALU_SLTS || operator_i == ALU_SRA || operator_i == ALU_LTS || operator_i == ALU_GES);
        case (semseg)
            4'd0: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= (((!ANreg[5] & operand_b_i[31]) || (!ANreg[7] & operand_a_i[31]) || (!ANreg[3] & result_o[31])) && minus) ? 7'b1111110: 7'b0000001;
            4'd1: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= (((!ANreg[5] & operand_b_i[31]) || (!ANreg[7] & operand_a_i[31]) || (!ANreg[3] & result_o[31])) && minus) ? 7'b1001110: 7'b1001111;
            4'd2: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0010010;
            4'd3: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000110;
            4'd4: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1001100;
            4'd5: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0100100;
            4'd6: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0100000;
            4'd7: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001111;
            4'd8: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000000;
            4'd9: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000100;
        endcase
    end
end

endmodule