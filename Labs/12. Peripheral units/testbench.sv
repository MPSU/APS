//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin

// Module Name:    tb_riscv_unit
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T

// Description: tb for peripheral units
//////////////////////////////////////////////////////////////////////////////////

module tb_riscv_unit();

localparam variant = 'd1; //1-SW_LED; 2-PS2_HEXLED; 3-UART;
localparam button = 8'h16; //keyboard key code

logic clk;
logic ps2_clk;
logic ps2_dat;
logic resetn;
logic [15:0] sw_i;
logic [15:0] led_o;
logic parity; 
logic starter;

logic [ 6:0] hex_led_o;  
logic [ 7:0] hex_sel_o;
logic        rx_i;
logic        tx_o;
  
initial begin clk = 0; ps2_clk = 0; end

always #50 clk = ~clk;
always #50000 if (variant == 2) if(starter || (cntr > 0)) ps2_clk = ~ps2_clk; else ps2_clk = 1;

logic [11:0] data;

initial begin
  resetn = 1;
  repeat(2)@(posedge clk);
  resetn = 0;
  repeat(2) @(posedge clk);
  resetn = 1;
end

riscv_unit dut(
  .clk_i    (clk      ),
  .resetn_i (resetn   ),
  .sw_i     (sw_i     ),
  .led_o    (led_o    ),
  .kclk_i   (ps2_clk  ),
  .kdata_i  (ps2_dat  ),
  .hex_led_o(hex_led_o),
  .hex_sel_o(hex_sel_o),
  .rx_i     (rx_i     ),
  .tx_o     (tx_o     )
);

logic [3:0] cntr;

always @(negedge ps2_clk) begin
  if(starter || (cntr > 0))
    if(cntr == 10)
      cntr <= 0;
    else
      cntr <= cntr + 1;        
end
assign ps2_dat = cntr>0? data[cntr-1] : 1;

initial begin
  sw_i = 16'h0;
  cntr = 0;
  starter = 0;
  parity = !(^button);
  data = 0;
  case (variant)
  1: begin
    #10000;
    sw_i = 16'h01AA;
    #20000;
    sw_i = 16'hFF00;
  end
  2: begin
    data = {2'b11, parity, button, 1'b0};
    #100000;
    starter = 1;
    @(posedge ps2_clk)
    starter = 0;
  end
  3: begin
    
  end
  endcase

end


endmodule
