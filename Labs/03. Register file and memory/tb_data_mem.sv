//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Nikita Bulavin

// Module Name:    tb_data_mem
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for data memory
//////////////////////////////////////////////////////////////////////////////////

module tb_data_mem();

parameter ADDR_SIZE = 16384;
parameter TIME_OPERATION  = 20;
parameter STEP = 8;

    logic        CLK;
    logic        REQ;
    logic        WE;
    logic [31:0] A;
    logic [31:0] WD;
    logic [31:0] RD;

    data_mem DUT (
    .clk_i          (CLK),
    .mem_req_i      (REQ),
    .write_enable_i (WE ),
    .addr_i         (A  ),
    .write_data_i   (WD),
    .read_data_o    (RD)
    );

    logic [31:0] RDa;
    integer i, hash, err_count = 0;
    assign A = i;

    parameter CLK_FREQ_MHz   = 100;
    parameter CLK_SEMI_PERIOD= 1e3/CLK_FREQ_MHz/2;

    initial CLK <= 0;
    always #CLK_SEMI_PERIOD CLK = ~CLK;

    initial begin
        $timeformat(-9, 2, " ns", 3);
        $display( "\nStart test: \n\n==========================\nCLICK THE BUTTON 'Run All'\n==========================\n"); $stop();
        REQ = 1;
        WE = 0;
        @(posedge CLK);
        for (i = 0; i < ADDR_SIZE; i = i + STEP) begin
            hash = (i+4)*8/15*16/23*42;
            WE = 1;
            WD = hash;
            @(posedge CLK)#3;
        end
        WE = 0;
        @(posedge CLK);
        for (i = 0; i < ADDR_SIZE; i = i + STEP) begin
            @(posedge CLK)#3;
            hash = (i+4)*8/15*16/23*42;
            if(RD !== hash) begin
                $error("Read data: %0h is unequal written data: %0h at addres: %0h, time: %t", RD, hash, i, $time);
                err_count = err_count + 1;
            end
        end
        for (i = 0; i < (ADDR_SIZE+STEP); i = i + 1 + $urandom() % STEP) begin
            REQ = |($urandom %10);
            WE = 0;
            #TIME_OPERATION;
            RDa = RD;
            WD = $urandom;
            #TIME_OPERATION;
            WE = $urandom % 2;
            #TIME_OPERATION;
            if ((!WE && REQ) && RD !== RDa) begin
                $error("When reading (write_enable_i = %h), the data %h is overwritten with data %h at address %h, time: %t", WE, RDa, RD, A, $time);
                err_count = err_count + 1;
            end
            #TIME_OPERATION;
        end
        #TIME_OPERATION;
        REQ = 1;
        WE = 0;
        #TIME_OPERATION;
        for (i = 0; i < 4; i = i + 1) begin
          if(i==0) begin
            repeat(2)@(posedge CLK);
            #1; RDa = RD;
          end else
          if(RD !== RDa) begin
            $error("incorrect conversion of the reading address = %h, time: %t", A, $time);
            err_count = err_count + 1;
          end
          #TIME_OPERATION;
        end
        i = 0; WE = 0; REQ = 1;
        @(posedge CLK);
        @(negedge CLK);
        i = 4;
        #1; RDa = RD;
        @(posedge CLK); #1;
        if (RD == RDa) begin
            $error("reading from data memory must be synchronous, time: %t", $time);
            err_count = err_count + 1;
        end
        @(posedge CLK);
        $display("Number of errors: %d", err_count);
        if( !err_count )  $display("\ndata_mem SUCCESS!!!\n");
        $finish();
    end
endmodule
