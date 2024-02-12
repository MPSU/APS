//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Andrei Solodovnikov

// Module Name:    tb_fulladder4
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for 4-bit fulladder
//////////////////////////////////////////////////////////////////////////////////

module tb_fulladder4();

    logic [3:0] tb_a_i;
    logic [3:0] tb_b_i;
    logic       tb_carry_i;
    logic       tb_carry_o;
    logic [3:0] tb_sum_o;
    logic [8:0] test_case;

    fulladder4 DUT (
        .a_i(tb_a_i),
        .b_i(tb_b_i),
        .sum_o(tb_sum_o),
        .carry_i(tb_carry_i),
        .carry_o(tb_carry_o)
    );

    assign {tb_a_i, tb_b_i, tb_carry_i} = test_case;

    initial begin
      $display("Test has been started");
      $display( "\n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
      #5ns;
      test_case = 3'd0;
      repeat(512) begin
        #5ns;
        test_case++;
      end
      $display("\nTest has been finished\n");
      $finish();
    end

endmodule
