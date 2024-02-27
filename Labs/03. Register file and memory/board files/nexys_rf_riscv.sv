/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Alexander Kharlamov
* Email(s)       : sasha_xarlamov@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module nexys_rf_riscv(
  input  logic        clk_i,
  input  logic        arstn_i,
  input  logic [15:0] sw_i,
  input  logic        btnd_i,
  input  logic        btnr_i,
  output logic [15:0] led_o,
  output logic        ca_o,
  output logic        cb_o,
  output logic        cc_o,
  output logic        cd_o,
  output logic        ce_o,
  output logic        cf_o,
  output logic        cg_o,
  output logic        dp_o,
  output logic [ 7:0] an_o
);

  logic [ 4:0]     ra1;
  logic [ 4:0]     ra2;
  logic [ 4:0]     wa;
  logic [31:0]     wd;
  logic            we;
  logic [7:0][3:0] rd1;
  logic [7:0][3:0] rd2;

  rf_riscv rf_riscv (
    .clk_i            (clk_i),
    .read_addr1_i     (ra1  ),
    .read_addr2_i     (ra2  ),
    .write_addr_i     (wa   ),
    .write_data_i     (wd   ),
    .write_enable_i   (we   ),
    .read_data1_o     (rd1  ),
    .read_data2_o     (rd2  )
  );

  function automatic logic [6:0] hex2semseg(input logic [3:0] hex);
      unique case (hex)
        4'h0: return 7'b0000001;
        4'h1: return 7'b1001111;
        4'h2: return 7'b0010010;
        4'h3: return 7'b0000110;
        4'h4: return 7'b1001100;
        4'h5: return 7'b0100100;
        4'h6: return 7'b0100000;
        4'h7: return 7'b0001111;
        4'h8: return 7'b0000000;
        4'h9: return 7'b0000100;
        4'hA: return 7'b0001000;
        4'hB: return 7'b1100000;
        4'hC: return 7'b0110001;
        4'hD: return 7'b1000010;
        4'hE: return 7'b0110000;
        4'hF: return 7'b0111000;
      endcase
  endfunction

  localparam int COUNTER_WIDTH = 10;
  logic [COUNTER_WIDTH-1:0] counter_next;
  logic [COUNTER_WIDTH-1:0] counter_ff;
  assign counter_next = counter_ff + COUNTER_WIDTH'('b1);
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) counter_ff <= '0;
    else          counter_ff <= counter_next;
  end

  logic [7:0] an_ff;
  logic [7:0] an_next;
  logic       an_en;
  assign an_next = {an_ff[$left(an_ff)-1:0], an_ff[$left(an_ff)]};
  assign an_en   = ~|counter_ff;
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if      (!arstn_i) an_ff <= ~8'b1;
    else if (an_en)    an_ff <= an_next;
  end

  localparam bit [6:0] BLANK = 7'b1111111;

  logic [6:0] semseg;
  always_comb begin
    semseg = BLANK;

    unique case (1'b0)
      an_ff[0]: semseg = hex2semseg(rd2[0]);
      an_ff[1]: semseg = hex2semseg(rd2[1]);
      an_ff[2]: semseg = hex2semseg(rd2[2]);
      an_ff[3]: semseg = hex2semseg(rd2[3]);
      an_ff[4]: semseg = hex2semseg(rd1[0]);
      an_ff[5]: semseg = hex2semseg(rd1[1]);
      an_ff[6]: semseg = hex2semseg(rd1[2]);
      an_ff[7]: semseg = hex2semseg(rd1[3]);
    endcase
  end

  logic [2:0][4:0] addresses_next;
  assign           addresses_next = sw_i[14:0];
  logic [4:0]      wa_ff;
  logic [4:0]      ra1_ff;
  logic [4:0]      ra2_ff;
  logic [4:0]      wa_next;
  assign           wa_next = addresses_next[0];
  logic [4:0]      ra1_next;
  assign           ra1_next = addresses_next[2];
  logic [4:0]      ra2_next;
  assign           ra2_next = addresses_next[1];
  logic            addresses_en;
  assign           addresses_en = btnd_i;
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) begin
      wa_ff  <= '0;
      ra1_ff <= '0;
      ra2_ff <= '0;
    end else if (addresses_en) begin
      wa_ff  <= wa_next;
      ra1_ff <= ra1_next;
      ra2_ff <= ra2_next;
    end
  end
  assign wa  = wa_ff;
  assign ra1 = ra1_ff;
  assign ra2 = ra2_ff;

  logic [15:0] wd_ff;
  logic        wd_en;
  assign       wd_en = btnr_i;
  logic [15:0] wd_next;
  assign       wd_next = sw_i;
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) begin
      wd_ff <= '0;
    end else if (wd_en) begin
      wd_ff <= wd_next;
    end
  end
  assign wd = {16'b0, wd_ff};

  logic  we_ff;
  logic  we_next;
  assign we_next = wd_en;
  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) we_ff <= 1'b0;
    else          we_ff <= we_next;
  end
  assign we = we_ff;

  assign {ca_o, cb_o, cc_o, cd_o, ce_o, cf_o, cg_o} = semseg;
  assign dp_o = 1'b1;

  assign led_o = {1'b0, ra1, ra2, wa};;

  assign an_o = an_ff;

endmodule
