/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Nikita Bulavin
* Email(s)       : nekkit6@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module hex_digits(
  input  logic       clk_i,
  input  logic       rst_i,
  input  logic [3:0] hex0_i,    // Цифра, выводимой на нулевой (самый правый) индикатор
  input  logic [3:0] hex1_i,    // Цифра, выводимая на первый индикатор
  input  logic [3:0] hex2_i,    // Цифра, выводимая на второй индикатор
  input  logic [3:0] hex3_i,    // Цифра, выводимая на третий индикатор
  input  logic [3:0] hex4_i,    // Цифра, выводимая на четвертый индикатор
  input  logic [3:0] hex5_i,    // Цифра, выводимая на пятый индикатор
  input  logic [3:0] hex6_i,    // Цифра, выводимая на шестой индикатор
  input  logic [3:0] hex7_i,    // Цифра, выводимая на седьмой индикатор
  input  logic [7:0] bitmask_i, // Битовая маска для включения/отключения
                                // отдельных индикаторов

  output logic [6:0] hex_led_o, // Сигнал, контролирующий каждый отдельный
                                // светодиод индикатора
  output logic [7:0] hex_sel_o  // Сигнал, указывающий на какой индикатор
                                // выставляется hex_led
);

  logic [4:0] hex0, hex1, hex2, hex3, hex4, hex5, hex6, hex7;
  assign hex0 = {bitmask_i[0], hex0_i};
  assign hex1 = {bitmask_i[1], hex1_i};
  assign hex2 = {bitmask_i[2], hex2_i};
  assign hex3 = {bitmask_i[3], hex3_i};
  assign hex4 = {bitmask_i[4], hex4_i};
  assign hex5 = {bitmask_i[5], hex5_i};
  assign hex6 = {bitmask_i[6], hex6_i};
  assign hex7 = {bitmask_i[7], hex7_i};

  localparam pwm = 32'd1000;  //шим сегментов

  logic [9:0] counter;
  logic [4:0] semseg;
  logic [7:0] ANreg;
  logic [6:0] hex_ledr;

  assign hex_sel_o = ANreg;
  assign hex_led_o = hex_ledr;

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      counter <= 'b0;
      ANreg[7:0] <= 8'b11111111;
      hex_ledr <= 7'b1111111;
    end
    else begin
      if (counter < pwm) counter <= counter + 'b1;
      else begin
        counter <= 'b0;
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
        ANreg[0]: semseg <= hex0;
        ANreg[1]: semseg <= hex1;
        ANreg[2]: semseg <= hex2;
        ANreg[3]: semseg <= hex3;
        ANreg[4]: semseg <= hex4;
        ANreg[5]: semseg <= hex5;
        ANreg[6]: semseg <= hex6;
        ANreg[7]: semseg <= hex7;
      endcase
      case (semseg)
          5'h10: hex_ledr <= 7'b0000001;
          5'h11: hex_ledr <= 7'b1001111;
          5'h12: hex_ledr <= 7'b0010010;
          5'h13: hex_ledr <= 7'b0000110;
          5'h14: hex_ledr <= 7'b1001100;
          5'h15: hex_ledr <= 7'b0100100;
          5'h16: hex_ledr <= 7'b0100000;
          5'h17: hex_ledr <= 7'b0001111;
          5'h18: hex_ledr <= 7'b0000000;
          5'h19: hex_ledr <= 7'b0000100;
          5'h1A: hex_ledr <= 7'b0001000;
          5'h1B: hex_ledr <= 7'b1100000;
          5'h1C: hex_ledr <= 7'b0110001;
          5'h1D: hex_ledr <= 7'b1000010;
          5'h1E: hex_ledr <= 7'b0110000;
          5'h1F: hex_ledr <= 7'b0111000;
          default: hex_ledr <= 7'b1111111;
      endcase
    end
  end

endmodule
