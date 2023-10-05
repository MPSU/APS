package alu_opcodes_pkg;
localparam ALU_OP_WIDTH = 5;

localparam ALU_ADD  = 5'b00000;
localparam ALU_SUB  = 5'b01000;

localparam ALU_XOR  = 5'b00100;
localparam ALU_OR   = 5'b00110;
localparam ALU_AND  = 5'b00111;

// shifts
localparam ALU_SRA  = 5'b01101;
localparam ALU_SRL  = 5'b00101;
localparam ALU_SLL  = 5'b00001;

// comparisons
localparam ALU_LTS  = 5'b11100;
localparam ALU_LTU  = 5'b11110;
localparam ALU_GES  = 5'b11101;
localparam ALU_GEU  = 5'b11111;
localparam ALU_EQ   = 5'b11000;
localparam ALU_NE   = 5'b11001;

// set lower than operations
localparam ALU_SLTS = 5'b00010;
localparam ALU_SLTU = 5'b00011;

endpackage