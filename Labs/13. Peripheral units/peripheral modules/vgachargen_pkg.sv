/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Alexander Kharlamov
* Email(s)       : sasha_xarlamov@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
package vgachargen_pkg;

  parameter int unsigned HD = 640; // Display area
  parameter int unsigned HF = 16;  // Front porch
  parameter int unsigned HR = 96;  // Retrace/Sync
  parameter int unsigned HB = 48;  // Back Porch
  parameter int unsigned VD = 480;
  parameter int unsigned VF = 10;
  parameter int unsigned VR = 2;
  parameter int unsigned VB = 33;

  parameter int unsigned HTOTAL = HD + HF + HR + HB;
  parameter int unsigned VTOTAL = VD + VF + VR + VB;

  parameter int unsigned VGA_MAX_H_WIDTH = $clog2(HTOTAL);
  parameter int unsigned VGA_MAX_V_WIDTH = $clog2(VTOTAL);

  parameter int unsigned BITMAP_H_PIXELS   = 8;
  parameter int unsigned BITMAP_V_PIXELS   = 16;
  parameter int unsigned BITMAP_H_WIDTH    = $clog2(BITMAP_H_PIXELS);
  parameter int unsigned BITMAP_V_WIDTH    = $clog2(BITMAP_V_PIXELS);
  parameter int unsigned CH_T_DATA_WIDTH   = BITMAP_H_PIXELS * BITMAP_V_PIXELS;
  parameter int unsigned BITMAP_ADDR_WIDTH = $clog2(CH_T_DATA_WIDTH);
  parameter int unsigned CHARSET_COUNT     = 256;
  parameter int unsigned CH_T_ADDR_WIDTH   = $clog2(CHARSET_COUNT/2);

  parameter int unsigned CH_H_PIXELS        = HD / BITMAP_H_PIXELS;
  parameter int unsigned CH_V_PIXELS        = VD / BITMAP_V_PIXELS;
  parameter int unsigned CH_V_WIDTH         = $clog2(CH_V_PIXELS);
  parameter int unsigned CH_H_WIDTH         = $clog2(CH_H_PIXELS);
  parameter int unsigned CH_MAP_ADDR_WIDTH  = CH_V_WIDTH + CH_H_WIDTH;
  parameter int unsigned CH_MAP_DATA_WIDTH  = CH_T_ADDR_WIDTH + 1;
  parameter int unsigned COL_MAP_ADDR_WIDTH = CH_MAP_ADDR_WIDTH;

  typedef enum logic [23:0] {
    COL_0  = 24'h000000,
    COL_1  = 24'h0000d8,
    COL_2  = 24'h00d800,
    COL_3  = 24'h00d8d8,
    COL_4  = 24'hd80000,
    COL_5  = 24'hd800d8,
    COL_6  = 24'hd8d800,
    COL_7  = 24'hd8d8d8,
    COL_9  = 24'h0000ff,
    COL_10 = 24'h00ff00,
    COL_11 = 24'h00ffff,
    COL_12 = 24'hff0000,
    COL_13 = 24'hff00ff,
    COL_14 = 24'hffff00,
    COL_15 = 24'hffffff
  } rgb_t;

  function automatic logic [11:0] rgb2half(rgb_t rgb_i);
    return {rgb_i[23:20], rgb_i[15:12], rgb_i[7:4]};
  endfunction

  function automatic logic [11:0] color_decode(logic [3:0] color_encoded_i);
    unique case (color_encoded_i)
      4'h0   : return rgb2half(COL_0 );
      4'h1   : return rgb2half(COL_1 );
      4'h2   : return rgb2half(COL_2 );
      4'h3   : return rgb2half(COL_3 );
      4'h4   : return rgb2half(COL_4 );
      4'h5   : return rgb2half(COL_5 );
      4'h6   : return rgb2half(COL_6 );
      4'h7   : return rgb2half(COL_7 );
      4'h8   : return rgb2half(COL_0 );
      4'h9   : return rgb2half(COL_9 );
      4'ha   : return rgb2half(COL_10);
      4'hb   : return rgb2half(COL_11);
      4'hc   : return rgb2half(COL_12);
      4'hd   : return rgb2half(COL_13);
      4'he   : return rgb2half(COL_14);
      4'hf   : return rgb2half(COL_15);
      default: return rgb2half(COL_0 );
    endcase
  endfunction
endpackage
