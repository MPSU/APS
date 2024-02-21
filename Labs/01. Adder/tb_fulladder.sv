/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

module tb_fulladder();

    logic tb_a_i;
    logic tb_b_i;
    logic tb_carry_i;
    logic tb_carry_o;
    logic tb_sum_o;
    logic [2:0] test_case;

    fulladder DUT (
        .a_i(tb_a_i),
        .b_i(tb_b_i),
        .sum_o(tb_sum_o),
        .carry_i(tb_carry_i),
        .carry_o(tb_carry_o)
    );

    assign {tb_a_i, tb_b_i, tb_carry_i} = test_case;

    initial begin
      $display("\nTest has been started\n");
      #5ns;
      test_case = 3'd0;
      repeat(8) begin
        #5ns;
        test_case++;
      end
      $display("\nTest has been finished\n");
      $finish();
    end

endmodule
