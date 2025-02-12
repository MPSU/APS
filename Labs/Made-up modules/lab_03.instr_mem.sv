/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module instr_mem
import memory_pkg::INSTR_MEM_SIZE_BYTES;
import memory_pkg::INSTR_MEM_SIZE_WORDS;
(
  input  logic [31:0] read_addr_i,
  output logic [31:0] read_data_o
);

  logic [31:0] ROM [INSTR_MEM_SIZE_WORDS];  // создать память с
                                            // <INSTR_MEM_SIZE_WORDS>
                                            // 32-битных ячеек

  initial begin
    $readmemh("program.mem", ROM);          // поместить в память ROM содержимое
  end                                       // файла program.mem

  // Реализация асинхронного порта на чтение, где на выход идет ячейка памяти
  // инструкций, расположенная по адресу read_addr_i, в котором отброшены два
  // младших бита, а также биты, двоичный вес которых превышает размер памяти
  //  данных в байтах.
  // Два младших бита отброшены, чтобы обеспечить выровненный доступ к памяти,
  // в то время как старшие биты отброшены, чтобы не дать обращаться в память
  // по адресам несуществующих ячеек (вместо этого будут выданы данные ячеек,
  // расположенных по младшим адресам).
  assign read_data_o = ROM[read_addr_i[$clog2(INSTR_MEM_SIZE_BYTES)-1:2]];

endmodule
