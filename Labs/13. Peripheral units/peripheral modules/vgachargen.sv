/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Alexander Kharlamov
* Email(s)       : sasha_xarlamov@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module vgachargen
  import vgachargen_pkg::*;
#(
  parameter int unsigned  CLK_FACTOR_25M           = 100 / 25,
  parameter               CH_T_INIT_FILE_NAME      = "lab_13_vga_ch_t.mem",
  parameter bit           CH_T_INIT_FILE_IS_BIN    = 1'b1,
  parameter               CH_MAP_INIT_FILE_NAME    = "lab_13_vga_ch_map.mem",
  parameter bit           CH_MAP_INIT_FILE_IS_BIN  = 1'b0,
  parameter               COL_MAP_INIT_FILE_NAME   = "lab_13_vga_col_map.mem",
  parameter bit           COL_MAP_INIT_FILE_IS_BIN = 1'b0
) (
  input  logic            clk_i,             // системный синхроимпульс
  input  logic            clk100m_i,         // клок с частотой 100МГц
  input  logic            rst_i,             // сигнал сброса

  /*
      Интерфейс записи выводимого символа
  */
  input  logic [ 9:0]     char_map_addr_i,   // адрес позиции выводимого символа
  input  logic            char_map_we_i,     // сигнал разрешения записи кода
  input  logic [ 3:0]     char_map_be_i,     // сигнал выбора байтов для записи
  input  logic [31:0]     char_map_wdata_i,  // ascii-код выводимого символа
  output logic [31:0]     char_map_rdata_o,  // сигнал чтения кода символа

  /*
      Интерфейс установки цветовой схемы
  */
  input  logic [ 9:0]     col_map_addr_i,    // адрес позиции устанавливаемой схемы
  input  logic            col_map_we_i,      // сигнал разрешения записи схемы
  input  logic [ 3:0]     col_map_be_i,      // сигнал выбора байтов для записи
  input  logic [31:0]     col_map_wdata_i,   // код устанавливаемой цветовой схемы
  output logic [31:0]     col_map_rdata_o,   // сигнал чтения кода схемы

  /*
      Интерфейс установки шрифта.
  */
  input  logic [ 9:0]     char_tiff_addr_i,  // адрес позиции устанавливаемого шрифта
  input  logic            char_tiff_we_i,    // сигнал разрешения записи шрифта
  input  logic [ 3:0]     char_tiff_be_i,    // сигнал выбора байтов для записи
  input  logic [31:0]     char_tiff_wdata_i, // отображаемые пиксели в текущей позиции шрифта
  output logic [31:0]     char_tiff_rdata_o, // сигнал чтения пикселей шрифта

  output logic [3:0]      vga_r_o,           // красный канал vga
  output logic [3:0]      vga_g_o,           // зеленый канал vga
  output logic [3:0]      vga_b_o,           // синий канал vga
  output logic            vga_hs_o,          // линия горизонтальной синхронизации vga
  output logic            vga_vs_o           // линия вертикальной синхронизации vga
);
  logic vga_clk_i;
  assign vga_clk_i = clk100m_i;

if (CLK_FACTOR_25M == 0 || CLK_FACTOR_25M > 4) error_unsupported_factor error_unsupported_factor ();

  logic  [3:0] char_map_be_gated;
  assign       char_map_be_gated = char_map_be_i & {4{char_map_we_i}};

  logic  [3:0] col_map_be_gated;
  assign       col_map_be_gated  = col_map_be_i & {4{col_map_we_i}};

  logic  [3:0] char_tiff_be_gated;
  assign       char_tiff_be_gated  = char_tiff_be_i & {4{char_tiff_we_i}};

  logic  arstn_i;
  assign arstn_i = ~rst_i;

  logic [VGA_MAX_H_WIDTH-1:0] hcount_pixels;
  logic [VGA_MAX_V_WIDTH-1:0] vcount_pixels;

  logic       pixel_enable;
  logic       pixel_enable_delayed;

  delay #(
    .DATA_WIDTH (1),
    .DELAY_BY   (2)
  ) pixel_enable_delay (
    .clk_i   (vga_clk_i),
    .arstn_i (arstn_i),
    .data_i  (pixel_enable),
    .data_o  (pixel_enable_delayed)
  );

  logic vga_vs_delayed;
  logic vga_vs;

  delay #(
    .DATA_WIDTH (1),
    .DELAY_BY   (2)
  ) vga_vs_delay (
    .clk_i   (vga_clk_i),
    .arstn_i (arstn_i),
    .data_i  (vga_vs),
    .data_o  (vga_vs_delayed)
  );

  logic vga_hs_delayed;
  logic vga_hs;

  delay #(
    .DATA_WIDTH (1),
    .DELAY_BY   (2)
  ) vga_hs_delay (
    .clk_i   (vga_clk_i),
    .arstn_i (arstn_i),
    .data_i  (vga_hs),
    .data_o  (vga_hs_delayed)
  );


  vga_block #(
    .CLK_FACTOR_25M (CLK_FACTOR_25M)
  ) vga_block (
    .clk_i          (vga_clk_i),
    .arstn_i        (arstn_i),
    .hcount_o       (hcount_pixels),
    .vcount_o       (vcount_pixels),
    .pixel_enable_o (pixel_enable),
    .vga_hs_o       (vga_hs),
    .vga_vs_o       (vga_vs)
  );

  logic [CH_MAP_ADDR_WIDTH-1:0] ch_map_addr_internal;

  logic [BITMAP_ADDR_WIDTH-1:0] bitmap_addr;
  logic [BITMAP_ADDR_WIDTH-1:0] bitmap_addr_delayed;

  delay #(
    .DATA_WIDTH (BITMAP_ADDR_WIDTH),
    .DELAY_BY   (2)
  ) bitmap_delay (
    .clk_i   (vga_clk_i),
    .arstn_i (arstn_i),
    .data_i  (bitmap_addr),
    .data_o  (bitmap_addr_delayed)
  );

  index_generator index_generator (
    .vcount_i      (vcount_pixels),
    .hcount_i      (hcount_pixels),
    .ch_map_addr_o (ch_map_addr_internal),
    .bitmap_addr_o (bitmap_addr)
  );

  logic [1:0] ch_map_byte_select;
  logic [1:0] ch_map_byte_select_delayed;
  assign      ch_map_byte_select = ch_map_addr_internal[1:0];

  delay #(
    .DATA_WIDTH (2),
    .DELAY_BY   (1)
  ) ch_map_byte_select_delay (
    .clk_i   (vga_clk_i),
    .arstn_i (arstn_i),
    .data_i  (ch_map_byte_select),
    .data_o  (ch_map_byte_select_delayed)
  );

  logic [CH_T_ADDR_WIDTH-1:0] ch_t_addr_internal;

  logic [3:0][7:0] ch_map_data_word;

  assign ch_t_addr_internal = ch_map_data_word[ch_map_byte_select_delayed];

  true_dual_port_rw_bram #(
    .INIT_FILE_NAME   (CH_MAP_INIT_FILE_NAME),
    .INIT_FILE_IS_BIN (CH_MAP_INIT_FILE_IS_BIN),
    .ADDR_WIDTH       (10)
  ) ch_map (
    .clka_i  (clk_i),
    .clkb_i  (vga_clk_i),
    .addra_i (char_map_addr_i),
    .addrb_i (ch_map_addr_internal[$left(ch_map_addr_internal):2]),
    .wea_i   (char_map_be_gated),
    .dina_i  (char_map_wdata_i),
    .douta_o (char_map_rdata_o),
    .doutb_o (ch_map_data_word)
  );

  logic [CH_T_DATA_WIDTH-1:0] ch_t_data_internal;

  logic [CH_T_ADDR_WIDTH-1:0] char_tiff_addr_128bit;
  assign                      char_tiff_addr_128bit = char_tiff_addr_i[$left(char_tiff_addr_i):2];
  logic [1:0]                 char_tiff_addr_offset_32bit;
  assign                      char_tiff_addr_offset_32bit = char_tiff_addr_i[1:0];

  logic [3:0][3:0]            char_tiff_wea;

  always_comb begin : bin2onehot
    char_tiff_wea                              = '0;
    char_tiff_wea[char_tiff_addr_offset_32bit] = char_tiff_be_gated;
  end

  logic [6:0]                 char_tiff_addr_offset_128bit;
  logic [6:0]                 char_tiff_addr_offset_128bit_ff;
  assign                      char_tiff_addr_offset_128bit = {char_tiff_addr_offset_32bit, 5'b00000};

  logic [127:0]               char_tiff_wdata_128bit;

  always_comb begin
    char_tiff_wdata_128bit                                   = '0;
    char_tiff_wdata_128bit[char_tiff_addr_offset_128bit+:32] = char_tiff_wdata_i;
  end

  logic [127:0]               char_tiff_rdata_128bit;

  assign                      char_tiff_rdata_o      = char_tiff_rdata_128bit[char_tiff_addr_offset_128bit_ff+:32];

  always_ff @(posedge clk_i) begin
    char_tiff_addr_offset_128bit_ff <= char_tiff_addr_offset_128bit;
  end

  true_dual_port_rw_bram #(
    .INIT_FILE_NAME   (CH_T_INIT_FILE_NAME),
    .INIT_FILE_IS_BIN (CH_T_INIT_FILE_IS_BIN),
    .NUM_COLS         (16),
    .COL_WIDTH        (8),
    .ADDR_WIDTH       (CH_T_ADDR_WIDTH)
  ) char_tiff (
    .clka_i  (clk_i),
    .clkb_i  (vga_clk_i),
    .addra_i (char_tiff_addr_128bit),
    .addrb_i (ch_t_addr_internal),
    .wea_i   (char_tiff_wea),
    .dina_i  (char_tiff_wdata_128bit),
    .douta_o (char_tiff_rdata_128bit),
    .doutb_o (ch_t_data_internal)
  );

  logic [7:0] col_map_data_internal;
  logic [7:0] col_map_data_internal_delayed;

  logic [3:0][7:0] col_map_data_internal_word;

  assign col_map_data_internal = col_map_data_internal_word[ch_map_byte_select_delayed];

  delay #(
    .DATA_WIDTH (8),
    .DELAY_BY   (1)
  ) col_map_data_delay (
    .clk_i   (vga_clk_i),
    .arstn_i (arstn_i),
    .data_i  (col_map_data_internal),
    .data_o  (col_map_data_internal_delayed)
  );

  logic [3:0] fg_col_map_data;
  logic [3:0] bg_col_map_data;

  assign fg_col_map_data = col_map_data_internal_delayed[7:4];
  assign bg_col_map_data = col_map_data_internal_delayed[3:0];

  true_dual_port_rw_bram #(
    .INIT_FILE_NAME   (COL_MAP_INIT_FILE_NAME),
    .INIT_FILE_IS_BIN (COL_MAP_INIT_FILE_IS_BIN),
    .ADDR_WIDTH       (10)
  ) col_map (
    .clka_i  (clk_i),
    .clkb_i  (vga_clk_i),
    .addra_i (col_map_addr_i),
    .addrb_i (ch_map_addr_internal[$left(ch_map_addr_internal):2]),
    .wea_i   (col_map_be_gated),
    .dina_i  (col_map_wdata_i),
    .douta_o (col_map_rdata_o),
    .doutb_o (col_map_data_internal_word)
  );

  logic   currentPixel;
  assign  currentPixel = ch_t_data_internal[bitmap_addr_delayed];

  logic [11:0] fg_color;
  assign  fg_color = color_decode(fg_col_map_data);

  logic [11:0] bg_color;
  assign  bg_color = color_decode(bg_col_map_data);

  // register outputs
  logic [3:0] vga_r_ff;
  logic [3:0] vga_r_next;
  logic [3:0] vga_g_ff;
  logic [3:0] vga_g_next;
  logic [3:0] vga_b_ff;
  logic [3:0] vga_b_next;
  logic       vga_vs_ff;
  logic       vga_vs_next;
  logic       vga_hs_ff;
  logic       vga_hs_next;

  assign vga_r_next = pixel_enable_delayed ? (currentPixel ? fg_color[11:8]: bg_color[11:8]) : '0;
  assign vga_g_next = pixel_enable_delayed ? (currentPixel ? fg_color[7:4] : bg_color[7:4])  : '0;
  assign vga_b_next = pixel_enable_delayed ? (currentPixel ? fg_color[3:0] : bg_color[3:0])  : '0;

  assign vga_vs_next = vga_vs_delayed;
  assign vga_hs_next = vga_hs_delayed;

  always_ff @(posedge vga_clk_i or negedge arstn_i) begin
    if (!arstn_i) begin
      vga_r_ff  <= '0;
      vga_g_ff  <= '0;
      vga_b_ff  <= '0;
      vga_hs_ff <= '0;
      vga_vs_ff <= '0;
    end else begin
      vga_r_ff  <= vga_r_next;
      vga_g_ff  <= vga_g_next;
      vga_b_ff  <= vga_b_next;
      vga_hs_ff <= vga_hs_next;
      vga_vs_ff <= vga_vs_next;
    end
  end

  assign vga_r_o = vga_r_ff;
  assign vga_g_o = vga_g_ff;
  assign vga_b_o = vga_b_ff;

  assign vga_hs_o = vga_hs_ff;
  assign vga_vs_o = vga_vs_ff;

endmodule

module clk_divider # (
  parameter int unsigned DIVISOR = 2
) (
  input  logic                       clk_i,
  input  logic                       arstn_i,
  output logic                       strb_o
);

  localparam int unsigned COUNTER_WIDTH = $clog2(DIVISOR);

  logic [COUNTER_WIDTH-1:0] counter_next;
  logic [COUNTER_WIDTH-1:0] counter_ff;

  assign counter_next = ~|counter_ff ? COUNTER_WIDTH'(DIVISOR - 1) : (counter_ff - COUNTER_WIDTH'(1));

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if   (~arstn_i) counter_ff <= '0;
    else            counter_ff <= counter_next;
  end

  logic strb_ff;
  logic strb_next;

  assign strb_next = ~|counter_ff;

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if   (~arstn_i) strb_ff <= '0;
    else            strb_ff <= strb_next;
  end

  assign strb_o = strb_ff;

endmodule

module delay #(
  parameter int unsigned DATA_WIDTH = 8,
  parameter int unsigned DELAY_BY   = 2
) (
  input  logic                  clk_i,
  input  logic                  arstn_i,
  input  logic [DATA_WIDTH-1:0] data_i,
  output logic [DATA_WIDTH-1:0] data_o
);
  logic [DELAY_BY-1:0][DATA_WIDTH-1:0] data_ff  ;
  logic [DELAY_BY-1:0][DATA_WIDTH-1:0] data_next;

  if   (DELAY_BY == 1) begin
    assign data_next = data_i;
    assign data_o    = data_ff;
  end else begin
    assign data_next = {data_ff[DELAY_BY-2:0], data_i};
    assign data_o    = data_ff[DELAY_BY-1];
  end

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if (!arstn_i) data_ff <= '0;
    else          data_ff <= data_next;
  end
endmodule

module index_generator
  import vgachargen_pkg::*;
(
  input  logic [VGA_MAX_V_WIDTH  -1:0] vcount_i,
  input  logic [VGA_MAX_H_WIDTH  -1:0] hcount_i,

  output logic [CH_MAP_ADDR_WIDTH-1:0] ch_map_addr_o,
  output logic [BITMAP_ADDR_WIDTH-1:0] bitmap_addr_o
);

  logic [CH_H_WIDTH-1:0] haddr_chars;
  logic [CH_V_WIDTH-1:0] vaddr_chars;

  assign haddr_chars = CH_H_WIDTH'(hcount_i >> BITMAP_H_WIDTH);
  assign vaddr_chars = CH_V_WIDTH'(vcount_i >> BITMAP_V_WIDTH);

  `define _MULT_BY_80(_x) ((_x << 6) + (_x << 4))
  assign ch_map_addr_o = `_MULT_BY_80(vaddr_chars) + haddr_chars;
  `undef _MULT_BY_80

  logic [BITMAP_H_WIDTH-1:0] haddr_pixels;
  logic [BITMAP_V_WIDTH-1:0] vaddr_pixels;

  assign haddr_pixels = hcount_i[BITMAP_H_WIDTH-1:0];
  assign vaddr_pixels = vcount_i[BITMAP_V_WIDTH-1:0];

  `define _MULT_BY_8(_x) (_x << 3)
  assign bitmap_addr_o = `_MULT_BY_8(vaddr_pixels) + haddr_pixels;
  `undef _MULT_BY_8


endmodule

module timing_generator
  import vgachargen_pkg::*;
(
  input  logic                       clk_i,
  input  logic                       arstn_i,
  input  logic                       en_i,

  output logic                       vga_hs_o,
  output logic                       vga_vs_o,

  // Display timing counters
  output logic [VGA_MAX_H_WIDTH-1:0] hcount_o,
  output logic [VGA_MAX_V_WIDTH-1:0] vcount_o,
  output logic                       pixel_enable_o

);

  logic [VGA_MAX_H_WIDTH-1:0] hcount_ff;
  logic [VGA_MAX_H_WIDTH-1:0] hcount_next;

  logic [VGA_MAX_V_WIDTH-1:0] vcount_ff;
  logic vcount_en;
  logic [VGA_MAX_V_WIDTH-1:0] vcount_next;

  // Horizontal counter
  assign hcount_next = ( hcount_ff < ( HTOTAL - 1 ) ) ? ( hcount_ff + 1 ) : ( '0 );
  always_ff @ ( posedge clk_i or negedge arstn_i )
    if      ( ~arstn_i  ) hcount_ff <= '0;
    else if (en_i)        hcount_ff <= hcount_next;

  // Vertical counter
  assign vcount_en   = ( hcount_ff == ( HTOTAL - 1 ) ) & en_i;
  assign vcount_next = ( vcount_ff < ( VTOTAL - 1 ) ) ? ( vcount_ff + 1 ) : ( '0 );
  always_ff @( posedge clk_i or negedge arstn_i )
    if      ( ~arstn_i    ) vcount_ff <= '0;
    else if ( vcount_en   ) vcount_ff <= vcount_next;

  enum {
    DISPLAY_S,
    FRONT_S,
    SYNC_S,
    BACK_S
  } hstate_ff, hstate_next,
    vstate_ff, vstate_next;

  always_ff @( posedge clk_i or negedge arstn_i )
    if( ~arstn_i ) begin
      hstate_ff <= DISPLAY_S;
      vstate_ff <= DISPLAY_S;
    end else if (en_i) begin
      hstate_ff <= hstate_next;
      vstate_ff <= vstate_next;
    end

  always_comb begin
    hstate_next = hstate_ff;
    unique case( hstate_ff)
      DISPLAY_S: if( hcount_ff == HD - 1 )           hstate_next = FRONT_S;

      FRONT_S:   if( hcount_ff == HD + HF - 1 )      hstate_next = SYNC_S;

      SYNC_S:    if( hcount_ff == HD + HF + HR - 1 ) hstate_next = BACK_S;

      BACK_S:    if( hcount_ff == HTOTAL - 1 )       hstate_next = DISPLAY_S;

      default:                                       hstate_next = DISPLAY_S;
    endcase
  end

  always_comb begin
    vstate_next = vstate_ff;
    if( vcount_en ) begin
      unique case( vstate_ff)
        DISPLAY_S: if( vcount_ff == VD - 1 )           vstate_next = FRONT_S;

        FRONT_S:   if( vcount_ff == VD + VF - 1 )      vstate_next = SYNC_S;

        SYNC_S:    if( vcount_ff == VD + VF + VR - 1 ) vstate_next = BACK_S;

        BACK_S:    if( vcount_ff == VTOTAL - 1 )       vstate_next = DISPLAY_S;

        default:                                       vstate_next = DISPLAY_S;
      endcase
    end
  end

  logic vga_vs_ff;
  logic vga_vs_next;

  assign vga_vs_next = vstate_next inside {DISPLAY_S, FRONT_S, BACK_S};

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if      (!arstn_i) vga_vs_ff <= 1'b1;
    else if (en_i)     vga_vs_ff <= vga_vs_next;
  end

  logic vga_hs_ff;
  logic vga_hs_next;

  assign vga_hs_next = hstate_next inside {DISPLAY_S, FRONT_S, BACK_S};

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if      (!arstn_i) vga_hs_ff <= 1'b1;
    else if (en_i)     vga_hs_ff <= vga_hs_next;
  end

  logic pixel_enable_ff;
  logic pixel_enable_next;

  assign pixel_enable_next = ( vstate_next == DISPLAY_S ) && ( hstate_next == DISPLAY_S );

  always_ff @(posedge clk_i or negedge arstn_i) begin
    if   (!arstn_i) pixel_enable_ff <= 1'b0;
    else if (en_i)  pixel_enable_ff <= pixel_enable_next;
  end

  assign vga_hs_o = vga_hs_ff;
  assign vga_vs_o = vga_vs_ff;

  assign pixel_enable_o = pixel_enable_ff;

  assign hcount_o = hcount_ff;
  assign vcount_o = vcount_ff;
endmodule

module true_dual_port_rw_bram #(
  parameter               INIT_FILE_NAME   = "",
  parameter               INIT_FILE_IS_BIN = 0,
  parameter  int unsigned COL_WIDTH        = 8,
  parameter  int unsigned NUM_COLS         = 4,
  parameter  int unsigned ADDR_WIDTH       = 4,
  localparam int unsigned DATA_WIDTH       = NUM_COLS * COL_WIDTH,
  localparam int unsigned DEPTH_WORDS      = 2 ** ADDR_WIDTH
) (
  input  logic                  clka_i,
  input  logic                  clkb_i,
  input  logic [ADDR_WIDTH-1:0] addra_i,
  input  logic [ADDR_WIDTH-1:0] addrb_i,
  input  logic [NUM_COLS  -1:0] wea_i,
  input  logic [DATA_WIDTH-1:0] dina_i,
  output logic [DATA_WIDTH-1:0] douta_o,
  output logic [DATA_WIDTH-1:0] doutb_o
);
  logic [DATA_WIDTH-1:0] mem[DEPTH_WORDS];

  if (INIT_FILE_NAME != "") begin                                                     : use_init_file
    if   (INIT_FILE_IS_BIN) initial  $readmemb(INIT_FILE_NAME, mem, 0, DEPTH_WORDS-1);
    else                    initial  $readmemh(INIT_FILE_NAME, mem, 0, DEPTH_WORDS-1);
  end else begin                                                                      : init_bram_to_zero
    initial begin
      for (int unsigned i = 0; i < DEPTH_WORDS; ++i) mem[i] = '0;
    end
  end

  always_ff @(posedge clka_i) begin
    for (int i = 0; i < NUM_COLS; ++i) begin
      if (wea_i[i]) mem[addra_i][i*COL_WIDTH+:COL_WIDTH] <= dina_i[i*COL_WIDTH+:COL_WIDTH];
    end
  end

  always_ff @(posedge clka_i) begin
    douta_o <= mem[addra_i];
  end

  always_ff @(posedge clkb_i) begin
    doutb_o <= mem[addrb_i];
  end

endmodule

module vga_block
  import vgachargen_pkg::*;
#(
  parameter int unsigned             CLK_FACTOR_25M = 4
) (
  input  logic                       clk_i,
  input  logic                       arstn_i,
  output logic [VGA_MAX_H_WIDTH-1:0] hcount_o,
  output logic [VGA_MAX_V_WIDTH-1:0] vcount_o,
  output logic                       pixel_enable_o,
  output logic                       vga_hs_o,
  output logic                       vga_vs_o
);
  logic clk_divider_strb;

if (CLK_FACTOR_25M > 1) begin
  clk_divider # (
    .DIVISOR (CLK_FACTOR_25M)
  ) clk_divider (
    .clk_i,
    .arstn_i,
    .strb_o  (clk_divider_strb)
  );
end else begin
  assign clk_divider_strb = 1'b1;
end

  timing_generator timing_generator (
    .clk_i,
    .arstn_i,
    .en_i     (clk_divider_strb),
    .vga_hs_o,
    .vga_vs_o,
    .hcount_o,
    .vcount_o,
    .pixel_enable_o

  );
endmodule
