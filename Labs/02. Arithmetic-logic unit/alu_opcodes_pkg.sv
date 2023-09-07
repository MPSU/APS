package alu_opcodes_pkg;
parameter ALU_OP_WIDTH = 5;

parameter ALU_ADD  = 5'b00000;
parameter ALU_SUB  = 5'b01000;

parameter ALU_XOR  = 5'b00100;
parameter ALU_OR   = 5'b00110;
parameter ALU_AND  = 5'b00111;

// shifts
parameter ALU_SRA  = 5'b01101;
parameter ALU_SRL  = 5'b00101;
parameter ALU_SLL  = 5'b00001;

// comparisons
parameter ALU_LTS  = 5'b11100;
parameter ALU_LTU  = 5'b11110;
parameter ALU_GES  = 5'b11101;
parameter ALU_GEU  = 5'b11111;
parameter ALU_EQ   = 5'b11000;
parameter ALU_NE   = 5'b11001;

// set lower than operations
parameter ALU_SLTS = 5'b00010;
parameter ALU_SLTU = 5'b00011;

endpackage
