/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Daniil Strelkov
* Email(s)       : 8190948@edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

module lab_10_tb_csr();
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

csr_controller DUT(.*);

always #5 clk_i <= ~clk_i;

int err_count;

initial begin
  $display("\n\n===========================\n\nPress button 'Run All' (F3)\n\n===========================\n\n");
  $stop();
  err_count = 0;
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
  seq_write();

  $display("Simulation finished. Number of errors: %d", err_count);
  if( !err_count )  $display("\n csr_controller SUCCESS!!!\n");
  $finish;
end

initial begin
  automatic int not_stopped = 1;
  forever begin
    @(posedge clk_i);
    if((err_count >= 10) && not_stopped) begin
      $display("Simulation stopped after ten errors.");
      $stop();
      not_stopped = 0;
    end
  end
end
logic [31:0] data_ref;
logic [31:0] pc_ref;
logic [31:0] mcause_ref;
logic [11:0] addr [0:4] = { MIE_ADDR,
MTVEC_ADDR,
MSCRATCH_ADDR,
MEPC_ADDR,
MCAUSE_ADDR};

task seq_write();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
    @(posedge clk_i);
  addr_i          <= addr[i];
  opcode_i        <= CSR_RW;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  end
  clear();
  @(posedge clk_i);
end
endtask




assign pc_ref = write_enable_i ? pc_i : pc_ref;
assign mcause_ref = write_enable_i ? mcause_i : mcause_ref;

always_ff @(posedge clk_i) begin
  if (rst_i) data_ref = 0;
  if (write_enable_i)
  case(opcode_i)
    CSR_RW:  data_ref = rs1_data_i;
    CSR_RS:  data_ref = rs1_data_i  | read_data_o;
    CSR_RC:  data_ref = ~rs1_data_i & read_data_o;
    CSR_RWI: data_ref = imm_data_i;
    CSR_RSI: data_ref = imm_data_i | read_data_o;
    CSR_RCI: data_ref = ~imm_data_i & read_data_o;
    default: data_ref = data_ref;
  endcase
end

task clear();
  rst_i <= 1'b1;
  repeat(2)@(posedge clk_i);
  rst_i <= 1'b0;
endtask

//csrrw
task csrrw();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  opcode_i        <= CSR_RW;
  addr_i          <= addr[i];
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask
//csrrs
task csrrs();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  opcode_i        <= CSR_RS;
  addr_i          <= addr[i];
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask
//csrrc
task csrrc();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RC;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask

//csrrwi
task csrrwi();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RWI;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask

//csrrsi
task csrrsi();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RSI;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask

//csrrci
task csrrci();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RCI;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask

//csrr
task csrr();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RS;
  rs1_data_i      <= 0;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
end
endtask

//csrw
task csrw();
  trap_i          <= 0;
for (int i = 0; i<5; i = i+1) begin
  repeat(20) begin
  addr_i          <= addr[i];
  opcode_i        <= CSR_RW;
  rs1_data_i      <= $random;
  imm_data_i      <= $random;
  write_enable_i  <= 1;
  @(posedge clk_i);
  write_enable_i  <= 0;
  @(posedge clk_i);
  check_reg();
  end
  clear();
  @(posedge clk_i);
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
  trap_i          <= 0;
  opcode_i        <= 0;
  rs1_data_i      <= 0;
  imm_data_i      <= 0;
  write_enable_i  <= 0;
  for (int i = 0; i<5; i = i+1) begin
  addr_i          <= addr[i];
  @(posedge clk_i);
end
endtask

trap_mepc_a: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  $rose(trap_i) |-> ##1 (mepc_o === pc_i)
)else begin
        err_count++;
        $display("Incorrect mepc   on trap    :      mepc_o = %08h while it should be %08h.\n", $sampled(mepc_o), $sampled(pc_i));
    end


trap_mcause_a: assert property (
  @(posedge clk_i) disable iff ( rst_i )
  ($rose(trap_i) && (addr_i == MCAUSE_ADDR)) |-> ##1 (read_data_o === mcause_i)
)else begin
        err_count++;
        $display("Incorrect mcause on trap    : read_data_o = %08h while it should be %08h.\n", $sampled(read_data_o), $sampled(mcause_i));
    end

string reg_name;
string padding;
csr_read_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i || $changed(addr_i, @(posedge clk_i)))
  ( (opcode_i inside {CSR_RW, CSR_RS, CSR_RC, CSR_RWI, CSR_RSI, CSR_RCI} ) && write_enable_i) |=> (read_data_o === data_ref)
)else begin
        err_count++;
        case(addr_i)
          MIE_ADDR      : reg_name = "mie     ";
          MTVEC_ADDR    : reg_name = "mtvec   ";
          MSCRATCH_ADDR : reg_name = "mscratch";
          MEPC_ADDR     : reg_name = "mepc    ";
          MCAUSE_ADDR   : reg_name = "mcause  ";
          default       : reg_name = "ill_addr";
        endcase
        $display("Incorrect read from %s: read_data_o = %08h while it should be %08h.\n", reg_name, $sampled(read_data_o), $sampled(data_ref));
    end

mie_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((addr_i === MIE_ADDR) && $rose(write_enable_i)) |=> (mie_o === data_ref)
)else begin
        err_count++;
        $display("Incorrect value of mie_o    :       mie_o = %08h while it should be %08h.\n", $sampled(mie_o), $sampled(data_ref));
      end

mepc_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((addr_i === MEPC_ADDR) && $rose(write_enable_i)) |=> (mepc_o === data_ref)
)else begin
        err_count++;
        $display("Incorrect value of mepc_o   :      mepc_o = %08h while it should be %08h.\n", $sampled(mepc_o), $sampled(data_ref));
    end

mtvec_a: assert property (
  @(posedge clk_i) disable iff ( rst_i || trap_i )
  ((addr_i === MTVEC_ADDR) && $rose(write_enable_i)) |=> (mtvec_o === data_ref)
)else begin
        err_count++;
        $display("Incorrect value of mtvec_o  :     mtvec_o = %08h while it should be %08h.\n", $sampled(mtvec_o), $sampled(data_ref));
    end

mepc_stability_a: assert property (
  @(posedge clk_i) disable iff (rst_i)
  !(trap_i | (write_enable_i & (addr_i === MEPC_ADDR))) |=> $stable(mepc_o)
)else begin
        err_count++;
        $display("Illegal change of mepc val  : it should be stable while trap_i = 0 and there is no CSR instruction at MEPC_ADDR");
    end

mtvec_stability_a: assert property (
  @(posedge clk_i) disable iff (rst_i)
  !(write_enable_i & (addr_i === MTVEC_ADDR)) |=> $stable(mtvec_o)
)else begin
        err_count++;
        $display("Illegal change of mtvec val : it should be stable while there is no CSR instruction at MTVEC_ADDR");
    end

mie_stability_a: assert property (
  @(posedge clk_i) disable iff (rst_i)
  !(write_enable_i & (addr_i === MIE_ADDR)) |=> $stable(mie_o)
)else begin
        err_count++;
        $display("Illegal change of mie val   : it should be stable while there is no CSR instruction at MIE_ADDR");
    end

endmodule
