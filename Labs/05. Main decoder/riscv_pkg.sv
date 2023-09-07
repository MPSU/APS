package riscv_pkg;

  import alu_opcodes_pkg::*;

// opcodes
parameter LOAD_OPCODE     = 5'b00_000;
parameter MISC_MEM_OPCODE = 5'b00_011;
parameter OP_IMM_OPCODE   = 5'b00_100;
parameter AUIPC_OPCODE    = 5'b00_101;
parameter STORE_OPCODE    = 5'b01_000;
parameter OP_OPCODE       = 5'b01_100;
parameter LUI_OPCODE      = 5'b01_101;
parameter BRANCH_OPCODE   = 5'b11_000;
parameter JALR_OPCODE     = 5'b11_001;
parameter JAL_OPCODE      = 5'b11_011;
parameter SYSTEM_OPCODE   = 5'b11_100;

// dmem type load store
parameter LDST_B          = 3'b000;
parameter LDST_H          = 3'b001;
parameter LDST_W          = 3'b010;
parameter LDST_BU         = 3'b100;
parameter LDST_HU         = 3'b101;

// operand a selection
parameter OP_A_RS1        = 2'b00;
parameter OP_A_CURR_PC    = 2'b01;
parameter OP_A_ZERO       = 2'b10;

// operand b selection
parameter OP_B_RS2        = 3'b000;
parameter OP_B_IMM_I      = 3'b001;
parameter OP_B_IMM_U      = 3'b010;
parameter OP_B_IMM_S      = 3'b011;
parameter OP_B_INCR       = 3'b100;

// writeback source selection
parameter WB_EX_RESULT    = 1'b0;
parameter WB_LSU_DATA     = 1'b1;

endpackage