/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* File           : tb_miriscv_alu.sv
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Daniil Strelkov
* Email(s)       : 8190948@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module tb_alu();

import alu_opcodes_pkg::*;

parameter TEST_VALUES     = 1000;

logic clk = 0;
always #5ns clk = ~clk;

logic [4:0]  operator_i;
logic [31:0] operand_a_i;
logic [31:0] operand_b_i;

wire [31:0] result_dut;
wire        comparison_result_dut;

wire [31:0] result_ref;
wire        comparison_result_ref;


alu_riscv DUT
(
  .alu_op_i (operator_i ),
  .a_i      (operand_a_i),
  .b_i      (operand_b_i),

  .result_o (result_dut ),
  .flag_o   (comparison_result_dut)
);

alu_riscv_ref REF
(
  .alu_op_i (operator_i ),
  .a_i      (operand_a_i),
  .b_i      (operand_b_i),

  .result_o (result_ref ),
  .flag_o   (comparison_result_ref)
);

integer     i, err_cnt = 0;
reg [8*9:1] operator_type;

initial
  begin
    $display("Test has been started");
    $display( "\n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
    //X_test();
    result_test();
    flag_test();
    sign_test();
    shift_test();
    random_test();
    direct_test();
    $display("\nTest has been finished\nNumber of errors: %d\n", err_cnt);
    $finish();
  end

task X_test();
  repeat(TEST_VALUES)
  begin
    case($urandom_range(6))
      0: operator_i = 5'bx;
      default: operator_i = $urandom();
    endcase
    case($urandom_range(6))
      0: operand_a_i = 5'bx;
      default: operand_a_i = $urandom();
    endcase
    case($urandom_range(6))
      0: operand_b_i = 5'bx;
      default: operand_b_i = $urandom();
    endcase
    @(posedge clk);
  end
endtask

task result_test();
  repeat(TEST_VALUES)
  begin
    operator_i  = $urandom_range(4'b1111);
    operand_a_i = $urandom();
    operand_b_i = $urandom();
    @(posedge clk);
 end
endtask

task flag_test();
  repeat(TEST_VALUES)
  begin
    operator_i  = {2'b11, $urandom_range(3'b111)};
    operand_a_i = $urandom();
    operand_b_i = $urandom();
    @(posedge clk);
  end
endtask

task sign_test();
  repeat(TEST_VALUES)
  begin
    std::randomize(operator_i) with {operator_i inside {ALU_LTS ,ALU_GES, ALU_SLTS, ALU_SRA};};
    operand_a_i = $urandom();
    operand_b_i = $urandom();
    @(posedge clk);
  end
endtask

task shift_test();
  repeat(TEST_VALUES)
  begin
    std::randomize(operator_i) with {operator_i inside {ALU_SRL,ALU_SLL,ALU_SRA};};
    operand_a_i = $urandom();
    operand_b_i = $urandom();
    @(posedge clk);
  end
endtask

task random_test();
  repeat(TEST_VALUES)
  begin
    operator_i  = $urandom();
    operand_a_i = $urandom();
    operand_b_i = $urandom();
    @(posedge clk);
  end
endtask

task direct_test();

  logic [4:0] flag_opcodes_1[6] = {ALU_SLTS, ALU_SLTU, ALU_LTS, ALU_GES, ALU_LTU, ALU_GEU};
  logic [4:0] flag_opcodes_2[3] = {ALU_SLL, ALU_SRL, ALU_SRA};
  logic [4:0] flag_opcodes_3[2] = {ALU_ADD, ALU_SUB};
  logic [4:0] flag_opcodes_4[5] = {ALU_XOR, ALU_OR, ALU_AND, ALU_EQ, ALU_NE};
 
  repeat(100)
  begin
    std::randomize(operand_a_i, operand_b_i) with {operand_a_i==operand_b_i;};
    foreach(flag_opcodes_1[i]) begin
      operator_i = flag_opcodes_1[i];
      @(posedge clk);
    end
  end

  repeat(100)
  begin
    std::randomize(operand_a_i, operand_b_i) with {operand_a_i>operand_b_i;};
    foreach(flag_opcodes_1[i]) begin
      operator_i = flag_opcodes_1[i];
      @(posedge clk);
    end
  end

  repeat(100)
  begin
    std::randomize(operand_a_i, operand_b_i) with {operand_a_i<operand_b_i;};
    foreach(flag_opcodes_1[i]) begin
      operator_i = flag_opcodes_1[i];
      @(posedge clk);
    end
  end

  repeat(100)
  begin
    operand_a_i = $urandom();
    std::randomize(operand_b_i) with {operand_b_i<32;};
    foreach(flag_opcodes_2[i]) begin
      operator_i = flag_opcodes_2[i];
      @(posedge clk);
    end
  end

  repeat(100)
  begin
    operand_a_i = $urandom();
    operand_b_i = $urandom() & 5'b00000;
    foreach(flag_opcodes_2[i]) begin
      operator_i = flag_opcodes_2[i];
      @(posedge clk);
    end
  end

  repeat(100)
  begin
    std::randomize(operand_a_i) with {operand_a_i > {31{1'b1}};}; 
    std::randomize(operand_b_i) with {operand_b_i > {31{1'b1}};};
    foreach(flag_opcodes_3[i]) begin
      operator_i = flag_opcodes_3[i];
      @(posedge clk);
    end
  end
    
  repeat(100)
  begin
    operand_a_i = $urandom();
    operand_b_i = $urandom();
    foreach(flag_opcodes_4[i]) begin
      operator_i = flag_opcodes_4[i];
      @(posedge clk);
    end
  end
endtask

always @(*) begin
  case(operator_i)
    ALU_ADD  : operator_type = "ALU_ADD  ";
    ALU_SUB  : operator_type = "ALU_SUB  ";
    ALU_XOR  : operator_type = "ALU_XOR  ";
    ALU_OR   : operator_type = "ALU_OR   ";
    ALU_AND  : operator_type = "ALU_AND  ";
    ALU_SRA  : operator_type = "ALU_SRA  ";
    ALU_SRL  : operator_type = "ALU_SRL  ";
    ALU_SLL  : operator_type = "ALU_SLL  ";
    ALU_LTS  : operator_type = "ALU_LTS  ";
    ALU_LTU  : operator_type = "ALU_LTU  ";
    ALU_GES  : operator_type = "ALU_GES  ";
    ALU_GEU  : operator_type = "ALU_GEU  ";
    ALU_EQ   : operator_type = "ALU_EQ   ";
    ALU_NE   : operator_type = "ALU_NE   ";
    ALU_SLTS : operator_type = "ALU_SLTS ";
    ALU_SLTU : operator_type = "ALU_SLTU ";
    default  : operator_type = "NOP      ";
  endcase
end

alu_check: assert property (
  @(negedge clk)
  (result_ref === result_dut) and (comparison_result_dut === comparison_result_ref)
)
else begin
  err_cnt++;
  $error("\nOperator    : %s\noperands    : a_i = 0x%08h, b_i = 0x%08h\nyour result : result = 0x%08h, flag = %b\nreference   : result = 0x%08h, flag = %b",
          operator_type, operand_a_i, operand_b_i, result_dut, comparison_result_dut, result_ref, comparison_result_ref);
  if(err_cnt == 10) begin
    $display("\nTest has been stopped after 10 errors");
    $stop();
  end
end

endmodule

parameter ALUOP_W = 5;
parameter OP_W = 32;
parameter SHIFT_W = $clog2(OP_W);
parameter STAGE_LEN = OP_W+1;
parameter HASH_LEN = 1000;
parameter START_CODING = 10366;
parameter START_MUX = START_CODING+100;

module alu_riscv_ref (
    input  logic [ALUOP_W-1:0] alu_op_i,
    input  logic [OP_W-1:0]    a_i,
    input  logic [OP_W-1:0]    b_i,
    output logic [OP_W-1:0]    result_o,
    output logic               flag_o
);



genvar i, j, k;

logic [OP_W-1:0]      skjfbsbgisg [0:STAGE_LEN-1];
logic [STAGE_LEN-1:0] flxvnlkamla;

logic [OP_W*2-1:0] jdiuqfjkvc;
logic [OP_W-1:0]   fgdhdsvr;

logic [16*4*HASH_LEN-1:0] fdhgdfbdgh;

logic [OP_W-1:0] vufdjj;
logic            srtdv;
logic [OP_W-1:0] ndsvsd;
logic            hkfvbd;

logic [OP_W-1:0] dgdvdfb;
logic [OP_W-1:0] hjfhdhyj;
logic [OP_W-1:0] dfbfjfnf;
logic [OP_W-1:0] tjthntnt;
logic [OP_W-1:0] ertertert;
logic [OP_W-1:0] jmgmgnb;
logic [OP_W-1:0] mghngfg;
logic [OP_W-1:0] sddsvsdd;
logic [OP_W-1:0] cvbcvc;
logic [OP_W-1:0] tyjtyn;
logic [OP_W-1:0] dfbdgt;
logic [OP_W-1:0] ergmd;
logic [OP_W-1:0] bdfvtym;
logic [OP_W-1:0] dfrjsdb;
logic [OP_W-1:0] hfndnfgd;
logic [OP_W-1:0] cvbvrht;
logic [OP_W-1:0] gmndfvs;

assign dgdvdfb = 'hf6f6bbbb;
assign hjfhdhyj = 'h6253a375;
assign dfbfjfnf = 'h8d2816e0;
assign tjthntnt = 'h30c73f9a;
assign ertertert = 'h28012f16;
assign jmgmgnb = 'h7a95b3f9;
assign mghngfg = 'hee30ab37;
assign sddsvsdd = 'hee30ab37;
assign cvbcvc = 'hbca437d8;
assign tyjtyn = 'h53df827d;
assign dfbdgt = 'ha4622754;
assign ergmd = 'hee3054f0;
assign bdfvtym = 'h62535cb2;
assign dfrjsdb = 'h2801d111;
assign hfndnfgd = 'h30c7c08d;
assign cvbvrht = 'ha462d8d3;
assign gmndfvs = 'hf6f6446c;

assign fdhgdfbdgh = {
   36'h3E41C6E20,
   36'h11B9B36BC,
   28'hCE94EDC,
   24'h77E32D,
   32'h3BB6F3AD,
   36'h85FD4BC65,
   20'hB3D9A,
   48'hBE20A0E086D2,
   36'h26ED9CDF4,
   8'h40,
   24'h0B4072,
   44'h12621D1BFA0,
   40'h9292D9C0E5,
   36'h5902A9C3F,
   28'h6F46EDC,
   56'h63F791F9F1D1ED,
   48'h6226D04FA727,
   32'h9C3B92E3,
   16'hEC45,
   16'hF449,
   56'h5F224CF30D83F5,
   24'h9DA507,
   44'h8174EF0041D,
   56'hB557B32F802A44,
   56'h15E9586A463E96,
   60'h7847AA0786A6B1D,
   56'h489E2B535C4538,
   32'hEB5509D7,
   28'hA96D029,
   52'h849A9581041BA,
   20'h181C6,
   36'hB77CF15DA,
   20'h1B10E,
   36'h8A76254FA,
   28'h9315088,
   4'h9,
   48'h16EE10CE91F2,
   20'h2CB47,
   20'h8A699,
   8'h9A,
   24'h82316F,
   40'h9DE20624F9,
   24'hF9E1DE,
   12'hC81,
   56'h0DB23F174F455B,
   32'h1957CE66,
   32'hC38DEE2B,
   4'hF,
   4'h0,
   44'h56CE783D0E2,
   56'hB261BCA0F00746,
   8'h5A,
   44'h83B6C5AEDF9,
   40'h1BD8F862B4,
   36'hD3D04A466,
   12'h3BB,
   4'h0,
   56'hCC3C36541EADF5,
   4'hA,
   28'hF8D4D49,
   28'h92CC18D,
   48'h70348675C0AD,
   56'hD97D10E10D8197,
   4'h5,
   20'hF48F5,
   8'h06,
   56'hC1143F3F3303AF,
   56'hAF5F315EAE57A6,
   28'hD1E5649,
   4'h9,
   8'h49,
   48'hD1F766BD868B,
   32'h181B8229,
   16'h0717,
   32'h8D29D699,
   8'hB4,
   48'hAF7850575F0C,
   52'hD49B3518569D7,
   44'h58010FECB4B,
   8'hAA,
   60'h7C757AB2B104631,
   28'h0A0E5F3,
   60'hEAF00B81398A69E,
   28'h1181CD4,
   56'hE13C80FA3DF770,
   36'hFDC738FD9,
   60'h994E0C5E2822DB6,
   16'hCB8F,
   12'h21E,
   52'hD843F1E0B6631,
   12'h958,
   32'hBCEB9ECC,
   4'hA,
   56'hDD4124FD5405EA,
   4'hC,
   4'h6,
   8'hB7,
   44'h611BDAA2E2D,
   4'h8,
   48'h8E9EFAF044D5,
   20'hC086A,
   8'hB1,
   4'hF,
   48'hBD6994252CAB,
   28'h9630B33,
   36'h588D1A522,
   52'hA5AC97DB595AC,
   12'h8D7,
   44'h7AF48225646,
   48'h7FD3F6A14944,
   4'h1,
   32'hDEB3C0A0,
   60'hD6F539789CDA6D5,
   56'h049B878D5A0CEA,
   60'h1CC65E10DFE1459,
   8'h7B,
   24'hC62339,
   16'h0629,
   16'h42DC,
   4'hE,
   4'h4,
   32'h30B27628,
   12'hC57,
   56'h7E2B26C69E6A8D,
   20'h72A72,
   24'hC8EF00,
   40'hCBFAF0DA94,
   44'h061D258C8BA,
   28'h389AEAA,
   8'h41,
   56'hF331BF02A98521,
   48'h5DA3EDDE901E,
   36'h4A47DF994,
   4'hF,
   32'h2881D05C,
   8'h42,
   48'h49063F3513DD,
   4'h8,
   40'hF18EDA5CF5,
   20'h940EF,
   48'h2E66BE06F74A,
   16'h6FCA,
   48'h5AB9D53AE721,
   16'h8F48,
   8'hF8,
   60'h47F24EFE966C7CB,
   16'hCE7D,
   44'hE38743E2847,
   24'h02D46D,
   4'hB,
   56'hDCC747CF2F9CF3,
   4'h9,
   16'h1EDB,
   4'h5,
   8'h8F,
   8'h58,
   56'hD99B11A0CE5A95,
   40'hEC5E7D7339,
   28'hAE626F6,
   4'h3,
   8'hD4,
   28'h6628821,
   56'hF31A99E66A5F47,
   24'h1BDB2A,
   36'h8200410E7,
   8'hFD,
   16'hE089,
   48'h204F8F809B1F,
   36'hD4483BA93,
   4'hE,
   24'h174230,
   48'hF3D3241C38A0,
   36'h114570ADA,
   12'hBD9,
   4'h4,
   36'h2CE6A729F,
   36'hC0C0F0D7A,
   60'h4AA3B90ABB4CC5A,
   52'hEC478788E8388,
   52'hEE1213E9570CE,
   8'hB2,
   36'hE71136493,
   32'hD58CB9A8,
   60'h75AC3A0E955C2FD,
   4'h2,
   20'h37590,
   16'hC7FA,
   8'hBF,
   40'h41991D26EC,
   12'hBDA,
   28'h1E55962,
   60'h80FA229FB1F1A77,
   4'hE,
   16'hFD62,
   24'hFCEC51,
   16'h7DFA,
   28'h5A0D095,
   28'hB4EF0E3,
   24'hA5ABB8,
   36'h0B86E2117,
   28'hB4D9D92,
   56'h1DFBE3941D04D7,
   40'hF54058D7AD,
   24'h24E364,
   36'hCE94D0121,
   60'h24028166F96F46F,
   20'h75EC3,
   12'h342,
   44'h83AF0FC5D1F,
   16'h568E,
   20'h8E16C,
   44'h9FD58B9D9DA,
   28'h118C75D,
   48'h58A8F1804318,
   12'h0F0,
   4'hB,
   20'h373D0,
   60'hD283007D7874281,
   32'hFA5A8CD2,
   48'h0CC25C2A5907,
   4'h8,
   12'hBAD,
   16'h10B4,
   4'h1,
   48'h8FA365200285,
   8'h2A,
   28'h71770B7,
   4'h7,
   20'h9411D,
   12'h2D3,
   48'h6E47DC016D7A,
   60'h6CBCF6C67956753,
   8'hBE,
   56'h7FC9873962591F,
   28'hDEF169D,
   40'h6CC3401324,
   4'h3,
   52'hCBB5B9DD52F5E,
   16'hF771,
   8'hFA,
   32'hEE35A02B,
   8'hCF,
   4'hE,
   48'hDA5F2AEB5586,
   36'hAB791E841,
   40'h0C5FE90683,
   56'h750CB7BB4D61C7,
   4'h1,
   44'hCBCD9884B30,
   40'hF6C9792E07,
   52'hB27DD79FD0FFB,
   16'hEB7B,
   20'h92AEC,
   20'hF23FF,
   8'h35,
   56'h365FA3DD80AA76,
   8'h56,
   16'h5127,
   8'h36,
   32'h6C35B935,
   56'h7B61BFA30B2C2F,
   32'hDBA37CB7,
   48'hF3C3AF0F75F2,
   4'hC,
   8'hE1,
   4'h5,
   52'hA7E12FBE29A70,
   40'hF6BE206F78,
   36'h62342AD57,
   52'h9C94ED9906F6D,
   8'h90,
   40'hD24C961B05,
   24'h3B7DE2,
   60'h8F53A0BAAE87434,
   20'h04A47,
   48'hE3393E66CAE9,
   4'hE,
   32'hD5423515,
   16'h313A,
   16'h7D06,
   16'h8774,
   4'hA,
   8'h1F,
   16'hB381,
   52'h5621EB52E35F7,
   40'hD0FE3D352B,
   52'h189932A5F537F,
   60'h83AC2D6D4CB6E0A,
   28'h16FD492,
   40'h6A435388E9,
   60'h961A79498159FA3,
   56'hC3AD07FD3DBE9C,
   28'hB33AD29,
   60'h010A94FC8B05AB6,
   40'h3F47ABA652,
   4'h1,
   28'h8A47A17,
   8'hC8,
   40'h431235B3DE,
   8'hE3,
   20'h0E5E8,
   52'h005C69E3D1C5A,
   52'hF8F5E338E91E6,
   24'h4F0712,
   4'hE,
   20'h8D61A,
   20'h43F2F,
   28'h372D52F,
   52'h0368D061683DD,
   24'h96E906,
   12'h212,
   28'hD74D49E,
   8'h07,
   48'h013940352345,
   28'h11B0738,
   36'h9BF8DFCC5,
   4'h5,
   4'hB,
   24'h04255E,
   40'hE5C5EBD801,
   4'h4,
   20'h7F580,
   24'hABD566,
   56'hE625850E5CFD4E,
   56'h683E283C086EB7,
   40'hCBA41EAA18,
   40'h0D9C15E41E,
   40'hC147A317FE,
   60'h014B7B2AC3707D9,
   56'h1E5C7458A47DA3,
   44'h849D7934318,
   40'hF0FE18F61F,
   24'h8F3EBA,
   44'hD9EFC8EBAA3,
   4'h1,
   4'h3,
   44'hA75ADD4CC22,
   36'h07F230AA0,
   52'h758A2F74316D3,
   4'h2,
   8'hD6,
   48'hB842258F84CF,
   16'hBF5D,
   36'h90A89B820,
   16'hD630,
   40'hADD634783D,
   60'h5229B035DAB10B4,
   52'h55DF90B792E59,
   60'h6A735DCE7F30F1D,
   20'h3442B,
   4'hE,
   4'h6,
   40'h49F042E737,
   4'h7,
   28'hCC452E1,
   24'h960066,
   52'h257CF1D0E1DE1,
   20'hC062A,
   56'hB9FA5F4B295DD6,
   20'h7213D,
   8'h7C,
   24'h9601F7,
   36'h4CDA50E5C,
   4'h2,
   4'h8,
   24'h981426,
   60'h7A193150B32D258,
   32'h0F2B7906,
   28'h994EC0E,
   16'h27E7,
   60'h172FD33A0DD910B,
   32'hBF6CF786,
   32'h2283DC8E,
   48'hB30D84AAE5D3,
   16'h4BBC,
   40'h22A97394FE,
   44'h34906539AF9,
   52'hABCB8831CBDCC,
   12'h91D,
   8'hAC,
   32'h95713DD4,
   24'h101548,
   40'h9DC900686D,
   8'hB4,
   28'h71789B3,
   12'hEB7,
   40'h012122627B,
   48'h3F48538EE335,
   40'hEDCD27AC53,
   40'hC397B874E0,
   36'hFAD978A9C,
   12'hEE6,
   12'h2F8,
   60'h6F6E175E88291E5,
   20'h897B2,
   36'h3B079D6C8,
   44'hDCDD5375F3D,
   48'hAC2CCE714B2A,
   52'h0E36538037376,
   20'h653D0,
   12'hBC9,
   4'h0,
   56'h08818E0CE930E8,
   44'hD6F78B1EBB3,
   8'hD3,
   56'h842589D80B49E7,
   20'hDD604,
   60'h7BDCE63AD2DE2D5,
   8'h11,
   24'h74FCD0,
   20'h70A70,
   20'hADF6E,
   40'hBA2D49FBEE,
   4'hC,
   60'hEE5B847DD25929B,
   4'h4,
   16'hD3B6,
   56'hC2339627AC10E8,
   40'h18C518EDC7,
   52'h79350CC07DE0B,
   32'h0A66C5AC,
   4'h4,
   44'h350D8EAF53F,
   36'hFEC215459,
   36'h041F6D1DE,
   48'h37127B258A18,
   60'h8EC75B60D538D4A,
   28'h7119883,
   4'h8,
   56'h0C14543DD78C87,
   16'h2C3F,
   28'h95661DE,
   56'h8EB588008671E9,
   16'h0255,
   56'h69D63514572A97,
   48'h054FCAEC3652,
   60'hD19294E9FE143FC,
   20'hF2570,
   32'h5122ABE3,
   40'h00585DBC95,
   32'hED5E4618,
   52'h10CC68B80CC3C,
   12'h8A0,
   44'h6DEDA083A16,
   28'h2B7E8A4,
   20'h2FBA6,
   24'hAF27AA,
   56'hAF0EFD4CCDA680,
   4'h4,
   32'h30D730AC,
   12'hAB7,
   48'h39B55B230DD2,
   4'hE,
   48'h518EA168141B,
   60'hFB1EC0875933F3C,
   56'h40FD6D3213AD01,
   48'h53AE7FB8E718,
   16'hA818,
   48'h68199127E4EC,
   16'h6D00,
   24'h043523,
   36'h9F7349070,
   32'h15E2BE0D,
   56'h130D6101E5A1A0,
   44'h1BC88A0C6A3,
   48'h6B4100962260,
   4'h6,
   4'hE,
   40'hC41DA2ED9E,
   8'h1F,
   32'h6FC93981,
   24'h8DF791,
   4'h7,
   20'h8C957,
   56'h35B249B58EB6A2,
   12'h396,
   4'h2,
   56'h29CDA41A0A8EB8,
   24'hA681BB,
   60'h5F2877418D55C72,
   40'hBD7B88480B,
   4'hD,
   20'h7F0C9,
   4'hF,
   16'h7BA9,
   44'hAC7E4029125,
   32'hA3901193,
   4'h7,
   20'h17031,
   8'h2C,
   4'h7,
   32'h6A80D767,
   32'h742A1EE5,
   28'hAA6FD3D,
   56'h10B66012716EE2,
   36'hCBB850B1D,
   4'h2,
   28'hAA0861E,
   48'h2ECFE8A372B0,
   4'h5,
   28'hE4005BE,
   28'h2B70C09,
   12'h8F8,
   16'hA735,
   52'hA9B5BCE275589,
   36'h2D9A93517,
   28'h3A08509,
   48'hEC8F489E6823,
   4'hB,
   36'h2DE43C120,
   24'hF82F8E,
   28'hB1B83FE,
   32'h80FE7B67,
   56'h8A5E2CD1C40E2C,
   32'hA2D61B79,
   24'h55171F,
   16'h5211,
   8'hBD,
   16'hCBDA,
   36'h7B5374264,
   40'h87FA486E39,
   12'h3F1,
   20'hDEE39,
   28'h9E37D6A,
   12'h901,
   60'h477E119B4377374,
   12'h0C1,
   4'h6,
   60'hD6196339345458B,
   40'hA3BA40F9AB,
   36'hFEE72FA77,
   60'h8C6801EAAD98481,
   16'h4E38,
   56'h2367402A69FBB0,
   28'hB0E0C07,
   44'h630E97E4320,
   12'h460,
   60'h066D48EADCBD6CB,
   44'h13DA831732F,
   48'hC5AC2061BC88,
   56'hADB08E0C120894,
   40'h6A7898739C,
   8'h38,
   60'h6955D11C7215683,
   8'h03,
   16'h1011,
   32'hEAC10B28,
   4'h5,
   44'h32621E9662A,
   60'h6CC5F3EDD7B58B1,
   12'h005,
   32'hC44BFBD4,
   48'hCE5C0C0E675E,
   44'hCA88D1ECF49,
   44'h24D7620FCDD,
   20'hBE344,
   4'h3,
   4'h7,
   20'hA174B,
   48'hC7208449DAA0,
   48'hF020792D8513,
   48'h6D86F848EAE5,
   44'h9821963EF53,
   24'hAA3C48,
   28'h346E180,
   4'h5,
   8'hCD,
   44'h004E130E41A,
   8'h33,
   40'hF0E09FA395,
   24'h81FB5C,
   20'hE6909,
   60'h9AC3650570DE15D,
   56'h1606791551819F,
   8'h86,
   32'hE8A99CB9,
   52'h83E57E3422874,
   60'hA8C6543E7FF5676,
   16'h5676,
   12'hC6B,
   20'hC6855,
   48'h1A519A989D81,
   60'h50D9B033B92E2F8,
   4'h7,
   16'h3386,
   24'hA78EE5,
   60'h52CE743432E35F5,
   20'h166A2,
   60'hD54038E64D5457D,
   40'h681A545735,
   36'hFB11B0934,
   24'h3084A7,
   52'h8575B53373BD6,
   36'h83DF8F9AB,
   52'h80CDCF46BECDA,
   16'h26C8,
   60'hB586B4EE4003427,
   40'hC42468C69C,
   44'h6BCB869AAE9,
   20'hC2E35,
   4'hB,
   4'h2,
   56'h5DF766B2847904,
   4'h8,
   36'h7D53CA0AB,
   28'hAC3BB67,
   52'hEE44066D9FBD9,
   52'h877AA06D02AC8,
   56'hAF7557D99F8F22,
   32'h81D30D69,
   24'hEEBE73,
   28'h3387149,
   44'h18A46D03972,
   4'h0,
   60'h004D522A992FAE7,
   12'hD56,
   12'hF1A,
   8'h14,
   28'h33AE4F7,
   4'hE,
   40'hE8A7426D4F,
   32'h93E37738,
   52'h4CE8735C76768,
   24'h041D07,
   4'h3,
   56'h7E2F8E97D9E0AE,
   32'h9E6B0065,
   12'h899,
   12'h2DA,
   44'hFCA0DE398D6,
   4'h0,
   36'h29DD8202D,
   48'hC2FA50B786ED,
   44'hFA366C72ECC,
   4'h4,
   20'h5F253,
   28'h67B92FC,
   40'h45FC9700E8,
   48'h97DB3490407F,
   4'hB,
   32'hE4BEFDF9,
   52'h74F5DB18CBCEA,
   12'hDC7,
   12'h983,
   44'hCD030BAD004,
   32'hDD571232,
   8'hCE,
   40'h9002484D9D,
   20'h3C588,
   12'h0CE,
   32'hE09E3737,
   52'h82558704C9899,
   4'hC,
   32'hF6A46C70,
   28'h913E83A,
   60'h29379573616766A,
   32'h1C5AC3C2,
   60'h2938EBB1D130A72,
   56'hCF4B33A03A144A,
   28'h38DBBF7,
   20'h98764,
   36'hC180A97BC,
   52'hA5C2E210DD909,
   60'h7413E7D8F6C7FF1,
   20'hD99B2,
   20'h04A45,
   28'h29B6301,
   24'hEE408B,
   12'h77E,
   12'hBD7,
   16'hD534,
   16'hCB3F,
   12'hE7C,
   8'h11,
   36'hE4F9E739A,
   48'h435F32D3180E,
   60'hD2869C093707A92,
   20'h5F3B6,
   48'h7E41DF9E4197,
   56'h04A41E0B4D3512,
   60'hA2CB9D9AA6FD62A,
   44'h9E646102BF8,
   4'h7,
   4'hA,
   4'hA,
   4'hD,
   40'hC8AF1E15A8,
   36'h6F671C125,
   40'hE4E083EAD0,
   4'h8,
   28'hF9AF90A,
   52'hFFA2FA19C00B9,
   4'h9,
   12'h6E2,
   4'hE,
   20'h630FD,
   4'hD,
   12'hE71,
   60'h2866A15B3DEF97B,
   32'hA4F2D24A,
   12'hC69,
   48'h0ADD24E1270D,
   44'hD48E94BFBF6,
   52'h5138C7EE12570,
   40'hD2845FC7FE,
   40'hBC8A37D9D5,
   52'h78CBD51F316B1,
   8'h40,
   16'hF514,
   20'h6847A,
   32'h9624E2CE,
   28'hFA25C53,
   40'h016D52E09F,
   32'h0378D313,
   44'hD8F7877E214,
   44'h649F0FD601E,
   28'hE44CDB3,
   16'h2765,
   28'h085B24B,
   52'h612936E24410B,
   12'h0B6,
   52'h292B95DC411D3,
   52'hD6D861F5E0623,
   60'hF6C8C906A97C1A4,
   24'hCD4094,
   4'h6,
   8'h49,
   48'hEC5F254BCB9F,
   4'hC,
   20'hE5E67,
   44'h507E5AD05DE,
   4'h5,
   32'hB1170875,
   56'h650B86C8BFB344,
   44'hEF100564B42,
   48'hEA3DB1DFB2A0,
   4'h3,
   4'hC,
   48'h29C17FC95617,
   8'hFB,
   48'h8A8EABA7A19A,
   40'h3BB2B3F288,
   4'h8,
   56'h8741D4A2E08995,
   36'h30B9E16A3,
   40'hE63D066032,
   60'h9DA4875C5E7ABC8,
   36'h573897C92,
   56'h6523427FE7DC7E,
   20'hBCB55,
   60'hDF45363C1F3235F,
   8'h1F,
   8'h03,
   20'h87713,
   4'h1,
   12'hF62,
   32'h78CB9E4C,
   28'h091045A,
   60'h6292CE2DA2F04F7,
   28'h3A00AA2,
   8'h9F,
   56'hC15FC9A010CE34,
   24'h012D4B,
   60'h6B27A8C5C5D2A72,
   4'h3,
   8'hF9,
   36'h0C46EB938,
   52'h4766FD6EB9D9F,
   48'h8956830CD03A,
   8'h4E,
   40'h94A6838A5E,
   16'hEEA0,
   8'hCA,
   56'hA95DDF69936C92,
   32'h9AA3BAC6,
   36'h116C5BB49,
   52'hC85D8DC98A981,
   36'hC3DF43C0D,
   52'h7DCB6F8C29C0D,
   36'hAC1F25713,
   44'h9E13A18A490,
   24'h171FE7,
   36'hFE3C5B4B0,
   8'hA8,
   40'hFE9366B059,
   32'h464CD9C5,
   8'h14,
   36'hCD1D2AC39,
   28'h83BA5D8,
   4'h5,
   52'hBCD1F9E71F4A7,
   60'hEF17FBFA474D879,
   8'h57,
   20'hAB7C7,
   20'h850A7,
   4'h9,
   8'hA7,
   8'hB9,
   20'hEAF57,
   20'h0CF0D,
   36'hA66CBB05D,
   4'h7,
   56'h375C1741C206F5,
   4'h8,
   4'hF,
   32'h03677E76,
   36'hCC3A5396D,
   48'h5DC350FF15EA,
   60'h1D326602A672A7F,
   56'hFF2317649ED9BF,
   36'hB404E0CFE,
   60'h49D813BFE174335,
   48'h4513C431424D,
   36'hCF0DABCC6,
   32'hC118DA21,
   56'hA004D30115B64F,
   4'h6,
   32'h15DE2F02,
   36'h073B0966F,
   24'hBD9B05,
   48'h24F68F8330D5,
   12'h834,
   28'h55941F5,
   8'hCB,
   28'h87AE936,
   48'hE95C6B05BA5E,
   28'hA95732B,
   60'hA52EFBA48A81E18,
   60'h5352286F90BB598,
   20'hB3171,
   8'h89,
   40'h42754058ED,
   60'h7335AF47DA5D9CD,
   44'h35F33C3B85C,
   4'hB,
   32'h6B10E351,
   28'h35EAEBA,
   52'h0FD77A932EE38,
   20'hA8D85,
   60'h02DD83DE083A0B2,
   40'hF759605E60,
   52'hAD4BD59ADD1EA,
   48'hA0B31BD226EE,
   16'h3523,
   24'h43DA08,
   8'h11,
   40'h5B59899F72,
   44'h945A230F260,
   4'h8,
   48'hA135AE89A8FA,
   24'hCE7DAA,
   12'hA3B,
   20'h34012,
   12'h373,
   32'hEADEE44A,
   24'h8EB785,
   8'hF8,
   48'h4036D3C38C7C,
   48'h0A194E147AAF,
   12'h22C,
   4'hB,
   20'h3A3F2,
   16'hFC5C,
   20'hE61B0,
   24'h2F9D98,
   8'hF9,
   52'hB035B9FE7A925,
   8'hA7,
   4'hE,
   36'h60E1F3E5A,
   56'h411A52C7D9D6EC,
   56'h68E7DB14A9869F,
   4'h9,
   24'h536545,
   40'h170746597F,
   4'hB,
   40'h50B6E0C178,
   44'h2B84542511A,
   12'h88B,
   48'hFEADF5E5B509,
   16'hFF99,
   52'h732E37E11BCF6,
   4'h7,
   56'h14634938059E0C,
   16'h49C4,
   36'h072FC661E,
   44'h86F8569E4C8,
   36'hAD2AB8452,
   56'hFD344CF7C77FB0,
   20'h75E7B,
   4'hB,
   52'h3DD602755A0A8,
   4'h5,
   56'h87AF0D6DD004D2,
   20'hB99CC,
   20'hBB658,
   40'hF288DD7E72,
   52'h1713C3A3DC7FE,
   28'hE57B622,
   36'hA402D4A6D,
   16'h99A5,
   40'hB9DD847DD4,
   40'h5C2F02AD27,
   4'h7,
   20'h5897C,
   4'hF,
   8'h62,
   28'hB78707E,
   8'hC3,
   56'h7C07A72089CC51,
   32'hE8CAE910,
   52'h9FD533652FCC4,
   28'hC3DD30E,
   4'h5,
   32'h8005C6C8,
   16'h2717,
   16'hED9F,
   56'hF1AC2091DFCB87,
   28'h0E62441,
   4'hC,
   36'h563E35E8C,
   36'hC4850ADE1,
   20'hE7122,
   48'hD7745661D189,
   12'h0AA,
   8'h1D,
   36'h602C0849D,
   32'h5E29E3AF,
   4'hD,
   16'hE146,
   60'h57738EC7501816A,
   36'h9FA3E63DE,
   8'hFC,
   20'hC0C46,
   12'hF0A,
   40'h6E09EE41D5,
   28'hCD05875,
   32'h84CB60F1,
   56'h0E67566322DAB2,
   60'h1EB916F75DF732E,
   56'hFC8ADE386B57CB,
   24'hD1F785,
   4'h3,
   28'hF05AEBA,
   28'hFB9F260,
   4'h9,
   4'h0,
   48'h16BA47DCD1A0,
   52'h46BE2B3766BF8,
   8'h55,
   56'hA3F49E1F4B1EAB,
   36'h2B1C07AD5,
   32'h8C93F27B,
   16'hFC72,
   8'hE4,
   60'h9FEE92B60D849F8,
   48'h14A687B797DC,
   52'hD6ECDB36BE120,
   20'h95DE1,
   20'hF02E4,
   12'h35C,
   12'h6B4,
   4'h2,
   16'hFB08,
   24'hCAA271,
   28'h60E12CB,
   52'h6A2A4264AD27E,
   16'hF7AE,
   36'hFA54938BE,
   28'h69E69C1,
   28'h16F736E,
   4'h1,
   24'hA0B6A1,
   28'hA1BDF13,
   24'h47C773,
   48'h8D65A5117FBF,
   48'h93E5B7784515,
   16'h0FCC,
   24'hCF2F9A,
   36'h8601008B2,
   40'h8F5F0116A2,
   12'h703,
   8'hEF,
   60'h3EB9A7442A72FC7,
   60'h2ADECDD46EC41BF,
   44'hAA6D0D90961,
   28'h1DA1517,
   16'hFC73,
   12'h978,
   36'hA8EB52E2F,
   36'hCDCF325AF,
   28'hB792BF8,
   4'h3,
   36'h544100882,
   32'h6B2538C8,
   44'hEF0146D3D95,
   8'hB5,
   32'h029FBE2A,
   36'h8AA44CC8E,
   44'h7A738CA0CE4
};

assign flxvnlkamla = {alu_op_i,alu_op_i,alu_op_i,alu_op_i,alu_op_i,alu_op_i,alu_op_i};

assign vufdjj = {a_i[OP_W-1:OP_W/2], a_i[OP_W/2-1:0]};
assign ndsvsd = {b_i[OP_W-1:OP_W/2], b_i[OP_W/2-1:0]};
assign srtdv = skjfbsbgisg[STAGE_LEN-1][OP_W-1];
assign hkfvbd = skjfbsbgisg[STAGE_LEN-1][OP_W-2];

generate
    for (i = 0; i < 16; i += 1) begin
        for (j = 0; j < STAGE_LEN; j += 1) begin
            if (i == 0)
                if (j == 0) assign skjfbsbgisg[j] = fdhgdfbdgh[START_CODING+STAGE_LEN-1:START_CODING];
                else assign skjfbsbgisg[j] = {flxvnlkamla[j-1] ^ skjfbsbgisg[j-1][0] ^ skjfbsbgisg[j-1][OP_W/2],
                                       skjfbsbgisg[j-1][OP_W-1:1]
                                       } + 'hA;
        end
    end
endgenerate

assign jdiuqfjkvc = (vufdjj[OP_W-1] ? '1 : '0) << OP_W;
assign fgdhdsvr = (jdiuqfjkvc + vufdjj) >> ndsvsd[SHIFT_W-1:0];

assign result_o = skjfbsbgisg[STAGE_LEN-1] === dgdvdfb ? vufdjj | ndsvsd + (srtdv - hkfvbd) :
                  skjfbsbgisg[STAGE_LEN-1] === hjfhdhyj ? vufdjj + ndsvsd - srtdv :
                  skjfbsbgisg[STAGE_LEN-1] === dfbfjfnf ? (fgdhdsvr << hkfvbd) >> hkfvbd :
                  skjfbsbgisg[STAGE_LEN-1] === tjthntnt ? vufdjj & ndsvsd | srtdv & hkfvbd :
                  skjfbsbgisg[STAGE_LEN-1] === ertertert ? vufdjj < ndsvsd + srtdv :
                  skjfbsbgisg[STAGE_LEN-1] === jmgmgnb ? vufdjj ^ ndsvsd | srtdv :
                  skjfbsbgisg[STAGE_LEN-1] === mghngfg & skjfbsbgisg[STAGE_LEN-1][OP_W-1] ? $signed(vufdjj) < $signed(ndsvsd) :
                  skjfbsbgisg[STAGE_LEN-1] === sddsvsdd & ~skjfbsbgisg[STAGE_LEN-1][OP_W-1] ? $signed(srtdv) < $signed(hkfvbd) :
                  skjfbsbgisg[STAGE_LEN-1] === cvbcvc ? (vufdjj << ~srtdv) >> ndsvsd[SHIFT_W-1:0] :
                  skjfbsbgisg[STAGE_LEN-1] === tyjtyn ? vufdjj + srtdv - ndsvsd :
                  skjfbsbgisg[STAGE_LEN-1] === dfbdgt ? vufdjj << ndsvsd[SHIFT_W-1:0] << hkfvbd :
                  'b0;

assign flag_o = skjfbsbgisg[STAGE_LEN-1] === ergmd & skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? $signed(vufdjj) >= $signed(ndsvsd) :
                skjfbsbgisg[STAGE_LEN-1] === ergmd & ~skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? $signed(srtdv) >= $signed(hkfvbd) :
                skjfbsbgisg[STAGE_LEN-1] === bdfvtym & skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? vufdjj >= ndsvsd :
                skjfbsbgisg[STAGE_LEN-1] === bdfvtym & ~skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? srtdv >= hkfvbd :
                skjfbsbgisg[STAGE_LEN-1] === dfrjsdb & ~skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? $signed(vufdjj) < $signed(ndsvsd) :
                skjfbsbgisg[STAGE_LEN-1] === dfrjsdb & skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? $signed(srtdv) < $signed(hkfvbd) :
                skjfbsbgisg[STAGE_LEN-1] === hfndnfgd & ~skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? vufdjj == ndsvsd :
                skjfbsbgisg[STAGE_LEN-1] === hfndnfgd & skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? srtdv == hkfvbd :
                skjfbsbgisg[STAGE_LEN-1] === cvbvrht & ~skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? vufdjj < ndsvsd :
                skjfbsbgisg[STAGE_LEN-1] === cvbvrht & skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? srtdv < hkfvbd :
                skjfbsbgisg[STAGE_LEN-1] === gmndfvs & skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? vufdjj != ndsvsd :
                skjfbsbgisg[STAGE_LEN-1] === gmndfvs & ~skjfbsbgisg[STAGE_LEN-1][OP_W-2] ? srtdv != hkfvbd :
                'b0;

endmodule
