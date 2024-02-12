//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin

// Module Name:    tb_fulladder
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for 1-bit fulladder
//////////////////////////////////////////////////////////////////////////////////

module tb_fulladder();

parameter TIME_OPERATION  = 100;
parameter TEST_VALUES = 8;

    wire tb_a_i;
    wire tb_b_i;
    wire tb_carry_i;
    wire tb_carry_o;
    wire tb_sum_o;


    fulladder DUT (
        .a_i(tb_a_i),
        .b_i(tb_b_i),
        .sum_o(tb_sum_o),
        .carry_i(tb_carry_i),
        .carry_o(tb_carry_o)
    );

    integer     i;
    reg [4:0] running_line;
    reg [5*8-1:0] line_dump;

    assign tb_a_i = running_line[4];
    assign tb_b_i = running_line[3];
    assign tb_carry_i = running_line[2];

    initial begin
        $display("START simulation of 1-bit fulladder.");
        $display("You should run simmulation until the message 'FINISH simulation' appears in the log.");
        for (i = 0; i < TEST_VALUES; i = i + 1) begin
            running_line = line_dump[i*5+:5];
            #TIME_OPERATION;
        end
        $display("FINISH simulation");
        $display(
            "Now you should open the waveform window",
            "and visually prove correctness of the design"
        );

        $finish();
    end

    initial line_dump = {
    5'b00000,
    5'b10010,
    5'b01010,
    5'b11001,
    5'b00110,
    5'b10101,
    5'b01101,
    5'b11111};

endmodule
