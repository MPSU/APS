//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Andrei Solodovnikov

// Module Name:    tb_fulladder32
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for 32-bit fulladder
//////////////////////////////////////////////////////////////////////////////////

module tb_fulladder32();

    logic [31:0] tb_a_i;
    logic [31:0] tb_b_i;
    logic        tb_carry_i;
    logic        tb_carry_o;
    logic [31:0] tb_sum_o;

    logic clk = 0;
    always #5ns clk = ~clk;

    int err_cnt = 0;

    fulladder32 DUT (
        .a_i(tb_a_i),
        .b_i(tb_b_i),
        .sum_o(tb_sum_o),
        .carry_i(tb_carry_i),
        .carry_o(tb_carry_o)
    );

    initial begin
      $display("Test has been started");
      $display( "\n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
      sequential_add_test();
      random_test();
      $display("\nTest has been finished\nNumber of errors: %d\n", err_cnt);
      $finish();
    end

    task sequential_add_test();
      @(posedge clk);
      tb_a_i = 0;
      tb_b_i = 0;
      tb_carry_i = 0;
      @(posedge clk);
      for(int i = 0; i < 16; i++) begin
        tb_a_i += 256;
        for(int j = 0; j < 16; j++) begin
          tb_b_i += 256;
          tb_carry_i = ~tb_carry_i;
          @(posedge clk);
        end
      end
    endtask

    task random_test();
      repeat(1e4) begin
        tb_a_i     = $urandom();
        tb_b_i     = $urandom();
        tb_carry_i = $urandom_range(1);
        @(posedge clk);
      end
    endtask

    logic [32:0] reference;
    assign reference = {1'b0, tb_a_i} + {1'b0, tb_b_i} + tb_carry_i;

    sum_check: assert property (
      @(negedge clk)
      reference === {tb_carry_o, tb_sum_o}
    )
    else begin
      err_cnt++;
      $error("\noperands : a_i = 0x%08h, b_i = 0x%08h, carry_i = %b\nyour res : sum = 0x%08h, carry_o = %b\nreference: sum = 0x%08h, carry_o = %b",
             tb_a_i, tb_b_i, tb_carry_i, tb_sum_o, tb_carry_o, reference[31:0], reference [32]);
      if(err_cnt == 10) begin
        $display("\nTest has been stopped after 10 errors");
        $stop();
      end
    end
endmodule
