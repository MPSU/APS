/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/

package bluster_pkg;
  localparam INIT_MSG_SIZE  = 41;
  localparam FLASH_MSG_SIZE = 57;
  localparam ACK_MSG_SIZE   = 4;


/* -----------------------------------------------------------------------------
    Lab_15 tb tasks
*  -----------------------------------------------------------------------------
*/

  task automatic send_data(input byte mem[$], ref logic clk_i, tx_valid, tx_busy, ref logic [7:0] tx_data);
    for(int i = mem.size()-1; i >=0; i--) begin
      tx_data = mem[i];
      tx_valid = 1'b1;
      @(posedge clk_i);
      tx_valid = 1'b0;
      @(posedge clk_i);
      while(tx_busy) @(posedge clk_i);
    end
  endtask

  task automatic rcv_data(input int size, ref logic clk_i, rx_valid, tx_o, ref logic [7:0] rx_data);
    automatic logic [0:FLASH_MSG_SIZE-1][7:0] str;
    automatic logic [3:0][7:0] size_val;
    for(int i = 0; i < size; i++) begin
      @(posedge clk_i);
      while(!rx_valid)@(posedge clk_i);
      str[i] = rx_data;
      size_val[3-i] = rx_data;
    end
    case(size)
      INIT_MSG_SIZE: begin
        $display("%s", str[0:INIT_MSG_SIZE-2]);
        assert(str[0:INIT_MSG_SIZE-10] == "ready for flash starting from 0x")begin end
        else $error("Init message format is incorrect. Should be \"ready for flash starting from 0xADDR\"");
      end
      FLASH_MSG_SIZE: begin
        $display("%s", str[0:FLASH_MSG_SIZE-2]);
        assert((str[0:16] == "finished write 0x") && (str[25+:23] == " bytes starting from 0x"))begin end
        else $error("finish message format is incorrect. Should be \"finished write 0xSIZE bytes starting from 0xADDR\"");
      end
      ACK_MSG_SIZE : $display("%0d", size_val);
    endcase
    wait(tx_o);
  endtask

  task automatic program_region(input string fname, ref logic clk_i, tx_valid, rx_valid, tx_o, tx_busy, reset, ref logic [7:0] rx_data, tx_data);
    automatic int fd, start_addr;
    automatic logic [31:0] data;
    automatic byte mem[$];
    automatic byte str [4];
    automatic logic [3:0][7:0] size;
    $display("\n%0t. Start programming %s", $time, fname);
    fd = $fopen(fname, "r");
    assert(fd)
    else $fatal(1, "Can't open file %s", fname);
    void'($fscanf(fd, "@%x\w", start_addr));
    start_addr <<=2;
    while(!$feof(fd)) begin
      $fscanf(fd, "%x\w", data);
      mem.push_back(data[ 7: 0]);
      mem.push_back(data[15: 8]);
      mem.push_back(data[23:16]);
      mem.push_back(data[31:24]);
    end
    $fclose(fd);
    size = mem.size();
    str = {start_addr[7:0],start_addr[15:8],start_addr[23:16],start_addr[31:24]};
    send_data(str, clk_i, tx_valid, tx_busy, tx_data);
    rcv_data(INIT_MSG_SIZE, clk_i, rx_valid, tx_o, rx_data);
    str = {size[0],size[1],size[2],size[3]};
    send_data(str, clk_i, tx_valid, tx_busy, tx_data);
    rcv_data(ACK_MSG_SIZE, clk_i, rx_valid, tx_o, rx_data);
    send_data(mem, clk_i, tx_valid, tx_busy, tx_data);
    rcv_data(FLASH_MSG_SIZE, clk_i, rx_valid, tx_o, rx_data);
    $display("%0t. Region has been programmed", $time);
    assert(reset)
    else $error("Reset must be equal 1 while flashing is not done.");
  endtask

  task automatic finish_programming(ref logic clk_i, tx_valid, tx_busy, reset, ref logic [7:0] tx_data);
    automatic byte mem[$];
    mem.push_back(8'hff);
    mem.push_back(8'hff);
    mem.push_back(8'hff);
    mem.push_back(8'hff);
    send_data(mem, clk_i, tx_valid, tx_busy, tx_data);
    $display("Flashing is complete");
    assert(!reset)
    else $error("Reset must be equal 0 after flashing is complete.");
  endtask

  task automatic dummy_programming(ref logic clk_i, tx_valid, rx_valid, tx_o, tx_busy, reset, ref logic [7:0] rx_data, tx_data);
    automatic byte str [4] = {8'd0, 8'd0, 8'd0, 8'd0};
    rcv_data(INIT_MSG_SIZE, clk_i, rx_valid, tx_o, rx_data);
    send_data(str, clk_i, tx_valid, tx_busy, tx_data);
    rcv_data(ACK_MSG_SIZE, clk_i, rx_valid, tx_o, rx_data);
    rcv_data(FLASH_MSG_SIZE, clk_i, rx_valid, tx_o, rx_data);
    finish_programming(clk_i, tx_valid, tx_busy, reset, rx_data);
  endtask
endpackage