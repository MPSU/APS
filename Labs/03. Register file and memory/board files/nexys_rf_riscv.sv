/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module nexys_rf_riscv(
    input CLK100,
    input resetn,
    input BTND, BTNU, BTNL, BTNR, BTNC,
    input  [15:0] SW,
    output [15:0] LED,
    output CA, CB, CC, CD, CE, CF, CG, DP,
    output [7:0] AN,
    output LED16_B, LED16_G, LED16_R, LED17_B, LED17_G, LED17_R
    );

wire [31:0]     WD3;
wire            WE;
wire [31:0]     RD1;
wire [31:0]     RD2;

localparam pwm = 1000;
reg [9:0] counter;
reg [3:0] semseg;
reg [7:0] ANreg;
reg CAr, CBr, CCr, CDr, CEr, CFr, CGr, DPr;
reg [15:0] LEDr;

reg [4:0] a1;
reg [4:0] a2;
reg [4:0] a3;
reg [31:0] rd1;
reg [31:0] rd2;

rf_riscv DUT
(
  .clk_i            (CLK100 ),
  .read_addr1_i     (a1     ),
  .read_addr2_i     (a2     ),
  .write_addr_i     (a3     ),
  .write_data_i     (WD3    ),
  .write_enable_i   (WE     ),
  .read_data1_o     (RD1    ),
  .read_data2_o     (RD2    )
);

assign LED = {1'b0, a1, a2, a3};
assign AN[7:0] = ANreg[7:0];
assign {CA, CB, CC, CD, CE, CF, CG, DP} = {CAr, CBr, CCr, CDr, CEr, CFr, CGr, DPr};
assign LED16_G = BTNC | BTNR;
assign LED17_G = BTNL | BTNR;
assign {LED16_R, LED17_R} = {2{BTND}};
assign {LED16_B, LED17_B} = {2{BTNU}};

assign WD3 =  32'b0 | SW[15:0];
assign WE = BTND;


always @(posedge CLK100) begin
    if (!resetn) begin
        counter <= 'b0;
        ANreg[7:0] <= 8'b11111111;
        {CAr, CBr, CCr, CDr, CEr, CFr, CGr, DPr} <= 8'b11111111;
        {a1, a2, a3} <= 'b0;
        {rd1, rd2} <= 'b0;
    end 
    else begin
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
        a1 <= BTNL? SW[4:0]: a1;
        a2 <= BTNC? SW[4:0]: a2;
        a3 <= BTNR? SW[4:0]: a3;

        rd1 <= BTNU? RD1: rd1;
        rd2 <= BTNU? RD2: rd2;

        case (1'b0)
            ANreg[0]: begin
                semseg <= (rd2) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[1]: begin
                semseg <= (rd2 / 'h10) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[2]: begin
                semseg <= (rd2 / 'h100) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[3]: begin
                semseg <= (rd2 / 'h1000) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[4]: begin
                semseg <= (rd1) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[5]: begin
                semseg <= (rd1 / 'h10) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[6]: begin
                semseg <= (rd1 / 'h100) % 5'h10;
                //DPr <= 1'b1;
            end
            ANreg[7]: begin
                semseg <= (rd1 / 'h1000) % 5'h10;
                //DPr <= 1'b1;
            end
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
