/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module tb_daisy_chain();

logic clk_i, rst_i, ready_i, irq_ret_i;
logic [15:0] masked_irq_i;
logic  irq_o;
logic [15:0] irq_ret_o;
logic [31:0] irq_cause_o;

daisy_chain DUT(.*);

initial clk_i = 0;
always #5 clk_i = !clk_i;

initial begin
  rst_i <= 1'b1;
  @(posedge clk_i);
  rst_i <= 1'b0;
  mcause_onehot_test();
  random_test();
  $finish();
end

task mcause_onehot_test();
  ready_i      <= 1'b1;
  masked_irq_i <= 0;
  repeat (2**16) begin
    @(posedge clk_i);
    masked_irq_i <= masked_irq_i + 1'b1;
  end
endtask

task random_test();
  repeat(2**16) begin
  @(posedge clk_i);
    ready_i      <= $urandom_range(1);
    irq_ret_i    <= $urandom_range(1);
    masked_irq_i <= $urandom_range(2**16);
  end
endtask

logic [15:0] cause;

always_ff @(posedge clk_i) begin
  if(rst_i) begin
    cause <= '0;
  end
  else if(irq_o) begin
    cause <= irq_cause_o[19:4];
  end
end

irq_ret_o_is_not_0: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  !irq_ret_i |-> irq_ret_o === '0
)else $error("irq_ret_o are not equal 0");

irq_ret_o_is_incorrect: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  irq_ret_i |-> irq_ret_o === cause
)else $error("irq_ret_o are incorrect: %08h", irq_ret_o);

irq_o_is_not_1: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  ready_i & masked_irq_i |-> irq_o
)else $error("irq_o are not equal 1");

irq_o_is_not_0: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  !ready_i |-> !irq_o
)else $error("irq_o are not equal 0");

irq_cause_o_mcause: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  irq_o |-> $onehot0(irq_cause_o[19:4])
)else $error("error value on irq_cause_o: %08h, should be onehot", irq_cause_o[20:5]);

irq_cause_o_borders: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  irq_o |-> (irq_cause_o[31:20] === 12'h800) && (irq_cause_o[3:0] == 4'h0)
)else $error("irq_cause_o borders are incorrect: %08h", irq_cause_o);

endmodule