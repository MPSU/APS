//////////////////////////////////////////////////////////////////////////////////
// Company: MIET
// Engineer: Daniil Strelkov

// Module Name:    tb_csr
// Project Name:   RISCV_practicum
// Target Devices: Nexys A7-100T
// Description: tb for CSR controller
//
//////////////////////////////////////////////////////////////////////////////////


module tb_csr();
    logic     clk_i;
    logic     rst_i;
    logic     trap_i;
    
    logic [ 2:0] opcode_i;
    
    logic [11:0] addr_i; 
    logic [31:0] pc_i;
    logic [31:0] mcause_i;
    logic [31:0] rs1_data_i;
    logic [31:0] imm_data_i;
    logic        write_enable_i;
    
    logic [31:0] read_data_o;
    logic [31:0] mie_o;
    logic [31:0] mepc_o;
    logic [31:0] mtvec_o;

import csr_pkg::*;

csr_controller dut(.*);

always #5 clk_i <= ~clk_i;

int err_count;
bit not_stopped;
initial begin
  $display("\n\n===========================\n\nPress button 'Run All' (F3)\n\n===========================\n\n");
  $stop();
  err_count = 0;
  not_stopped = 1;
  clk_i <= 0;
  rst_i <= 1'b1;
  repeat(2)@(posedge clk_i);
  rst_i <= 1'b0;
end

initial begin
  opcode_i   = '0;
  addr_i     = '0;
  pc_i       = '0;
  mcause_i   = '0;
  rs1_data_i = '0;
  imm_data_i = '0;
  trap_i     = '0;
  repeat(4)@(posedge clk_i);
  csrrw();
  csrrs();
  csrrc();
  csrrwi();
  csrrsi();
  csrrci();
  csrr();
  csrw();
  trap();
  $display("Simulation finished. Number of errors: %d", err_count); 
  $finish();
end

logic [31:0] data_ref;
logic [31:0] pc_ref;
logic [31:0] mcause_ref;
logic [11:0] addr [0:4] = { MIE_ADDR,
MTVEC_ADDR,
MSCRATCH_ADDR,
MEPC_ADDR,
MCAUSE_ADDR};

assign pc_ref = write_enable_i ? pc_i : pc_ref;
assign mcause_ref = write_enable_i ? mcause_i : mcause_ref;
always_comb begin
  if (write_enable_i)
  case(opcode_i)
    CSR_RW:  data_ref <= #1 rs1_data_i;
    CSR_RS:  data_ref <= #1 rs1_data_i  | read_data_o;
    CSR_RC:  data_ref <= #1 ~rs1_data_i & read_data_o;
    CSR_RWI: data_ref <= #1 imm_data_i;
    CSR_RSI: data_ref <= #1 imm_data_i | read_data_o;
    CSR_RCI: data_ref <= #1 ~imm_data_i & read_data_o;
    default: data_ref <= #1 data_ref;
  endcase
end

task clear();
opcode_i <= CSR_RW;
rs1_data_i <= 0;
imm_data_i <= 0;
write_enable_i  <= 1;
@(posedge clk_i);
write_enable_i  <= 0;
@(posedge clk_i);
endtask

//csrrw
task csrrw();
trap_i   <= 0;
opcode_i <= CSR_RW;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
  clear();
end
endtask
//csrrs
task csrrs();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  opcode_i        <= CSR_RS;
  addr_i          <= addr[i];
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
  end
  clear();
end
endtask
//csrrc
task csrrc();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i <= CSR_RC;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
  clear();
end
endtask

//csrrwi
task csrrwi();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i <= CSR_RWI;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
  clear();
end
endtask

//csrrsi
task csrrsi();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i <= CSR_RSI;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
  clear();
end
endtask

//csrrci
task csrrci();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i <= CSR_RCI;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
  clear();
end
endtask

//csrr
task csrr();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i <= CSR_RS;
  rs1_data_i      <= 0;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
end
endtask

//csrw
task csrw();
trap_i   <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RW;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  check_reg();
end
end
endtask

//trap
task trap();
repeat(100) begin
  opcode_i        <= $random;
  addr_i          <= MCAUSE_ADDR;
  pc_i            <= $random;
  mcause_i        <= $random;
  write_enable_i  <= 0;
  trap_i   <= 1;
  @(posedge clk_i);
  trap_i   <= 0;
  @(posedge clk_i);
  check_reg();
end
endtask

task check_reg();
  trap_i   <= 0;
  for (int i = 0; i<5; i = i+1) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RS;
  rs1_data_i      <= 0;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
end
endtask

trap_a: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  (trap_i && (addr_i == MCAUSE_ADDR)) |-> ##1 (mepc_o === pc_i) && (read_data_o === mcause_i)
)else begin 
        err_count++;
        $error("\error write/read trap\n");
    end

csrrw_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ( (opcode_i === CSR_RW) && write_enable_i) |=> (read_data_o === data_ref) and (addr_i === MIE_ADDR) |-> (mie_o === data_ref) and (addr_i === MEPC_ADDR) |-> (mepc_o === data_ref) and (addr_i === MTVEC_ADDR) |-> (mtvec_o === data_ref)  
)else begin 
        err_count++;
        $error("\error write/read csrrw\n");
    end
    
csrrs_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((opcode_i === CSR_RS) && write_enable_i) |=> read_data_o === data_ref and (addr_i === MIE_ADDR) |-> (mie_o === data_ref) and (addr_i === MEPC_ADDR) |-> (mepc_o === data_ref) and (addr_i === MTVEC_ADDR) |-> (mtvec_o === data_ref)  
)else begin 
        err_count++;
        $error("\error write/read csrrs\n");
    end

csrrc_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((opcode_i === CSR_RC) && write_enable_i) |=> read_data_o === data_ref and (addr_i === MIE_ADDR) |-> (mie_o === data_ref) and (addr_i === MEPC_ADDR) |-> (mepc_o === data_ref) and (addr_i === MTVEC_ADDR) |-> (mtvec_o === data_ref)  
)else begin 
        err_count++;
        $error("\error write/read csrrc\n");
    end

csrrwi_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((opcode_i === CSR_RWI) && write_enable_i) |=> read_data_o === data_ref and (addr_i === MIE_ADDR) |-> (mie_o === data_ref) and (addr_i === MEPC_ADDR) |-> (mepc_o === data_ref) and (addr_i === MTVEC_ADDR) |-> (mtvec_o === data_ref)  
)else begin 
        err_count++;
        $error("\error write/read csrwi\n");
    end

csrrci_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((opcode_i === CSR_RCI) && write_enable_i ) |=> read_data_o === data_ref and (addr_i === MIE_ADDR) |-> (mie_o === data_ref) and (addr_i === MEPC_ADDR) |-> (mepc_o === data_ref) and (addr_i === MTVEC_ADDR) |-> (mtvec_o === data_ref)  
)else begin 
        err_count++;
        $error("\error write/read csrrci\n");
    end

csrrsi_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((opcode_i === CSR_RSI) && write_enable_i) |=> read_data_o === data_ref and (addr_i === MIE_ADDR) |-> (mie_o === data_ref) and (addr_i === MEPC_ADDR) |-> (mepc_o === data_ref) and (addr_i === MTVEC_ADDR) |-> (mtvec_o === data_ref)  
)else begin 
        err_count++;
        $error("\error write/read csrrsi\n");
    end


endmodule
