`timescale 1ns / 1ps

module nexys_riscv_unit(
    input CLK100,
    input resetn,
    input BTND,
    output CA, CB, CC, CD, CE, CF, CG, 
    output [7:0] AN
    );
    
    riscv_unit unit(
    .clk_i(btn),
    .rst_i(!resetn)
    );

  wire [31:0] instr_addr;
  wire [31:0] instr;
  reg   btn;
  
  assign instr_addr = unit.instr_addr;
  assign instr = unit.instr;

  localparam pwm = 1000;
  reg [9:0] counter;
  reg [7:0] semseg;
  reg [7:0] ANreg;
  reg CAr, CBr, CCr, CDr, CEr, CFr, CGr;

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
        if(|(~ANreg[5:4])) begin
            case (1'b0)
                ANreg[4]: semseg <= instr_addr[3:0];
                ANreg[5]: semseg <= instr_addr[7:4];
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
        end else begin
            case (1'b0)
                ANreg[7]: begin
                    {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0011000;
                end
                ANreg[6]: begin
                    {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0110001;
                end
                ANreg[3]: begin
                    case(instr[6:2])
                        5'b01101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111; //LUI   -
                        5'b00101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001000; //AUIP  A
                        5'b11011:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111; //JAL   -
                        5'b11001:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1000111; //JALR  J
                        5'b11000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1100000; //brch  b
                        5'b00000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //LOAd  L
                        5'b01000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0100100; //STOr  S
                        5'b00100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000001; //OPIM  O
                        5'b01100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111; //OP    -
                        default: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111001; //ILLE  I
                    endcase
                end
                ANreg[2]: begin
                    case(instr[6:2])
                        5'b01101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //LUI   L
                        5'b00101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1000001; //AUIP  U
                        5'b11011:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1000111; //JAL   J
                        5'b11001:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001000; //JALR  A
                        5'b11000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111010; //brch  r
                        5'b00000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000001; //LOAd  O
                        5'b01000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110000; //StOr  t
                        5'b00100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0011000; //OPIM  P
                        5'b01100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111111; //OP    -
                        default: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //ILLE  L
                    endcase
                end
                ANreg[1]: begin
                    case(instr[6:2])
                        5'b01101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1000001; //LUI   U
                        5'b00101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111001; //AUIP  I
                        5'b11011:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001000; //JAL   A
                        5'b11001:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //JALR  L
                        5'b11000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110010; //brch  c
                        5'b00000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0001000; //LOAd  A
                        5'b01000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000001; //STOr  O
                        5'b00100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111001; //OPIM  I
                        5'b01100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0000001; //OP    O
                        default: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //ILLE  L
                    endcase
                end
                ANreg[0]: begin
                    case(instr[6:2])
                        5'b01101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111001; //LUI   I
                        5'b00101:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0011000; //AUIP  P
                        5'b11011:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1110001; //JAL   L
                        5'b11001:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111010; //JALr  r
                        5'b11000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1101000; //brch  h
                        5'b00000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1000010; //LOAd  d
                        5'b01000:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b1111010; //STOr  r
                        5'b00100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0101010; //OPIM  M
                        5'b01100:{CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0011000; //OP    P
                        default: {CAr, CBr, CCr, CDr, CEr, CFr, CGr} <= 7'b0110000; //ILLE  E
                    endcase
                end
            endcase
         end
     end
     
  end

endmodule
