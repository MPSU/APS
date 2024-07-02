`include "../interface.sv"
module tb_vga();

  parameter [31:0] ADDR_CHAR_TOP_LEFT       = 32'h0;
  parameter [31:0] ADDR_CHAR_LEFT_IN_FIRST  = 32'h0000_0050;
  parameter [31:0] ADDR_CHAR_LOWER_RIGHT    = 32'h0000_095F;

  parameter [31:0] ADDR_COLOR_TOP_LEFT      = 32'h0000_1000;
  parameter [31:0] ADDR_COLOR_LEFT_IN_FIRST = 32'h0000_1050;
  parameter [31:0] ADDR_COLOR_LOWER_RIGHT   = 32'h0000_195F;

  /// color

  parameter [31:0] ASCI_A = 32'h41;

  // parameter [31:0] BITMAP_A [4] = {32'hFF, 32'h81, 32'hBD, 32'h81};
  // asci



  logic        clk_i;  
  logic        resetn_i;

  logic [31:0] addr;
  logic [31:0] last_read_data_o; 
  logic [31:0] data;

  logic [3:0] vga_r_o;
  logic [3:0]  vga_b_o;
  logic [3:0]  vga_g_o;
  logic        vga_hs_o;
  logic        vga_vs_o;
  logic [3:0]  mem_be_i;

  peripheral_if vga_if(clk_i);


  static logic [31:0] bitmap_a [4] = {32'hFF, 32'h81, 32'hBD, 32'h81};
  //static logic [31:0] address_list[3] = {ADR_SCAN_CODE, ADR_IS_UNREAD, ADR_RS2_RST};

  typedef enum {READ, WRITE} access_type_t;

  event uart_tx_reset;


  vga_sb_ctrl vga(
      .rst_i               (resetn_i                   ),
      .clk_i               (clk_i                      ),
      .req_i               (vga_if.req_i               ),
      .write_enable_i      (vga_if.write_enable_i      ),
      .addr_i              (vga_if.addr_i              ),
      .write_data_i        (vga_if.write_data_i        ),
      .read_data_o         (vga_if.read_data_o         ),
      .ready_o             (vga_if.ready_o             ),
      .vga_r_o             (vga_r_o),
      .vga_b_o             (vga_b_o),
      .vga_g_o             (vga_g_o),
      .vga_hs_o            (vga_hs_o),
      .vga_vs_o            (vga_vs_o),
      .mem_be_i            (mem_be_i)
    );


  task vga_write_char_map();


      @(posedge clk_i);

          last_read_data_o = vga_if.read_data_o;


      
          vga_if.write_request(ADDR_CHAR_LEFT_IN_FIRST, ASCI_A);
          assert(vga_if.read_data_o == last_read_data_o) else begin
              $error("Error"); end

  endtask



  task vga_read_char_map();
    
      @(posedge clk_i);
      
      vga_if.read_request(ADDR_CHAR_LEFT_IN_FIRST);

                 assert(vga_if.read_data_o == ASCI_A) else begin
              $error("Error"); end

  endtask



  task vga_write_color_map();

      @(posedge clk_i);

          last_read_data_o = vga_if.read_data_o;


      
          vga_if.write_request(ADDR_COLOR_LEFT_IN_FIRST, 32'hF0);
                    assert(vga_if.read_data_o == last_read_data_o) else begin
              $error("Error"); end 

  endtask



  task vga_read_color_map();
    
      @(posedge clk_i);
      
      vga_if.read_request(ADDR_COLOR_LEFT_IN_FIRST);
                 assert(vga_if.read_data_o == 32'hF0) else begin
              $error("Error"); end 

  endtask


  task vga_write_font_map();

    // for (int i = 0; i < 4; i++ ) begin
      @(posedge clk_i);
      
          vga_if.write_request((32'h00002000 ), bitmap_a[0]);
                    assert(vga_if.read_data_o == last_read_data_o) else begin
              $error("Error"); end
    // end

          @(posedge clk_i);
      
          vga_if.write_request((32'h00002FFF ), bitmap_a[1]);
                    assert(vga_if.read_data_o == last_read_data_o) else begin
              $error("Error"); end

  endtask



  task vga_read_font_map();
    
  //  for (int i = 0; i < 4; i++) begin
  
        @(posedge clk_i);
        
        vga_if.read_request(32'h00002000);
         assert(vga_if.read_data_o == bitmap_a[0])  else begin
              $error("Error"); end
  //  end

                  @(posedge clk_i);
        
        vga_if.read_request(32'h00002FFF);
         assert(vga_if.read_data_o == bitmap_a[0])  else begin
              $error("Error"); end
  endtask


  initial begin
    @(posedge clk_i);
    mem_be_i = 15;
    vga_write_char_map();
    vga_read_char_map();
    @(posedge clk_i);
    vga_write_color_map();
    vga_read_color_map();
    @(posedge clk_i);
    vga_write_font_map();
    vga_read_font_map();
    @(posedge clk_i);
    $finish;

  end


  initial begin
    clk_i = 0;
    forever #5 clk_i = ~clk_i;
  end

  initial begin
    resetn_i = 1;
  
    @(posedge clk_i);
  
    resetn_i = 0;

  end

endmodule