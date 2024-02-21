/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Alexey Kozin
* Email(s)       : @edu.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
module gpr_we_table (gis_ew_rpg, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_ew_rpg;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_ew_rpg = 1'b1;
        5'b00001: gis_ew_rpg = 1'b0;
        5'b00010: gis_ew_rpg = 1'b0;
        5'b00011: gis_ew_rpg = 1'b0;
        5'b00100: gis_ew_rpg = 1'b1;
        5'b00101: gis_ew_rpg = 1'b1;
        5'b00110: gis_ew_rpg = 1'b0;
        5'b00111: gis_ew_rpg = 1'b0;
        5'b01000: gis_ew_rpg = 1'b0;
        5'b01001: gis_ew_rpg = 1'b0;
        5'b01010: gis_ew_rpg = 1'b0;
        5'b01011: gis_ew_rpg = 1'b0;
        5'b01100: gis_ew_rpg = 1'b1;
        5'b01101: gis_ew_rpg = 1'b1;
        5'b01110: gis_ew_rpg = 1'b0;
        5'b01111: gis_ew_rpg = 1'b0;
        5'b10000: gis_ew_rpg = 1'b0;
        5'b10001: gis_ew_rpg = 1'b0;
        5'b10010: gis_ew_rpg = 1'b0;
        5'b10011: gis_ew_rpg = 1'b0;
        5'b10100: gis_ew_rpg = 1'b0;
        5'b10101: gis_ew_rpg = 1'b0;
        5'b10110: gis_ew_rpg = 1'b0;
        5'b10111: gis_ew_rpg = 1'b0;
        5'b11000: gis_ew_rpg = 1'b0;
        5'b11001: gis_ew_rpg = 1'b1;
        5'b11010: gis_ew_rpg = 1'b0;
        5'b11011: gis_ew_rpg = 1'b1;
        5'b11100: gis_ew_rpg = 1'b1;
        5'b11101: gis_ew_rpg = 1'b0;
        5'b11110: gis_ew_rpg = 1'b0;
        5'b11111: gis_ew_rpg = 1'b0;
    endcase
endmodule

module csr_we_table (gis_ew_rsc, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_ew_rsc;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_ew_rsc = 1'b0;
        5'b00001: gis_ew_rsc = 1'b0;
        5'b00010: gis_ew_rsc = 1'b0;
        5'b00011: gis_ew_rsc = 1'b0;
        5'b00100: gis_ew_rsc = 1'b0;
        5'b00101: gis_ew_rsc = 1'b0;
        5'b00110: gis_ew_rsc = 1'b0;
        5'b00111: gis_ew_rsc = 1'b0;
        5'b01000: gis_ew_rsc = 1'b0;
        5'b01001: gis_ew_rsc = 1'b0;
        5'b01010: gis_ew_rsc = 1'b0;
        5'b01011: gis_ew_rsc = 1'b0;
        5'b01100: gis_ew_rsc = 1'b0;
        5'b01101: gis_ew_rsc = 1'b0;
        5'b01110: gis_ew_rsc = 1'b0;
        5'b01111: gis_ew_rsc = 1'b0;
        5'b10000: gis_ew_rsc = 1'b0;
        5'b10001: gis_ew_rsc = 1'b0;
        5'b10010: gis_ew_rsc = 1'b0;
        5'b10011: gis_ew_rsc = 1'b0;
        5'b10100: gis_ew_rsc = 1'b0;
        5'b10101: gis_ew_rsc = 1'b0;
        5'b10110: gis_ew_rsc = 1'b0;
        5'b10111: gis_ew_rsc = 1'b0;
        5'b11000: gis_ew_rsc = 1'b0;
        5'b11001: gis_ew_rsc = 1'b0;
        5'b11010: gis_ew_rsc = 1'b0;
        5'b11011: gis_ew_rsc = 1'b0;
        5'b11100: gis_ew_rsc = 1'b1;
        5'b11101: gis_ew_rsc = 1'b0;
        5'b11110: gis_ew_rsc = 1'b0;
        5'b11111: gis_ew_rsc = 1'b0;
    endcase
endmodule



module mem_req_table (gis_qer_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_qer_mem;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_qer_mem = 1'b1;
        5'b00001: gis_qer_mem = 1'b0;
        5'b00010: gis_qer_mem = 1'b0;
        5'b00011: gis_qer_mem = 1'b0;
        5'b00100: gis_qer_mem = 1'b0;
        5'b00101: gis_qer_mem = 1'b0;
        5'b00110: gis_qer_mem = 1'b0;
        5'b00111: gis_qer_mem = 1'b0;
        5'b01000: gis_qer_mem = 1'b1;
        5'b01001: gis_qer_mem = 1'b0;
        5'b01010: gis_qer_mem = 1'b0;
        5'b01011: gis_qer_mem = 1'b0;
        5'b01100: gis_qer_mem = 1'b0;
        5'b01101: gis_qer_mem = 1'b0;
        5'b01110: gis_qer_mem = 1'b0;
        5'b01111: gis_qer_mem = 1'b0;
        5'b10000: gis_qer_mem = 1'b0;
        5'b10001: gis_qer_mem = 1'b0;
        5'b10010: gis_qer_mem = 1'b0;
        5'b10011: gis_qer_mem = 1'b0;
        5'b10100: gis_qer_mem = 1'b0;
        5'b10101: gis_qer_mem = 1'b0;
        5'b10110: gis_qer_mem = 1'b0;
        5'b10111: gis_qer_mem = 1'b0;
        5'b11000: gis_qer_mem = 1'b0;
        5'b11001: gis_qer_mem = 1'b0;
        5'b11010: gis_qer_mem = 1'b0;
        5'b11011: gis_qer_mem = 1'b0;
        5'b11100: gis_qer_mem = 1'b0;
        5'b11101: gis_qer_mem = 1'b0;
        5'b11110: gis_qer_mem = 1'b0;
        5'b11111: gis_qer_mem = 1'b0;
    endcase
endmodule

module mem_we_table (gis_ew_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_ew_mem;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_ew_mem = 1'b0;
        5'b00001: gis_ew_mem = 1'b0;
        5'b00010: gis_ew_mem = 1'b0;
        5'b00011: gis_ew_mem = 1'b0;
        5'b00100: gis_ew_mem = 1'b0;
        5'b00101: gis_ew_mem = 1'b0;
        5'b00110: gis_ew_mem = 1'b0;
        5'b00111: gis_ew_mem = 1'b0;
        5'b01000: gis_ew_mem = 1'b1;
        5'b01001: gis_ew_mem = 1'b0;
        5'b01010: gis_ew_mem = 1'b0;
        5'b01011: gis_ew_mem = 1'b0;
        5'b01100: gis_ew_mem = 1'b0;
        5'b01101: gis_ew_mem = 1'b0;
        5'b01110: gis_ew_mem = 1'b0;
        5'b01111: gis_ew_mem = 1'b0;
        5'b10000: gis_ew_mem = 1'b0;
        5'b10001: gis_ew_mem = 1'b0;
        5'b10010: gis_ew_mem = 1'b0;
        5'b10011: gis_ew_mem = 1'b0;
        5'b10100: gis_ew_mem = 1'b0;
        5'b10101: gis_ew_mem = 1'b0;
        5'b10110: gis_ew_mem = 1'b0;
        5'b10111: gis_ew_mem = 1'b0;
        5'b11000: gis_ew_mem = 1'b0;
        5'b11001: gis_ew_mem = 1'b0;
        5'b11010: gis_ew_mem = 1'b0;
        5'b11011: gis_ew_mem = 1'b0;
        5'b11100: gis_ew_mem = 1'b0;
        5'b11101: gis_ew_mem = 1'b0;
        5'b11110: gis_ew_mem = 1'b0;
        5'b11111: gis_ew_mem = 1'b0;
    endcase
endmodule

module branch_table (gis_hcnarb, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_hcnarb;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_hcnarb = 1'b0;
        5'b00001: gis_hcnarb = 1'b0;
        5'b00010: gis_hcnarb = 1'b0;
        5'b00011: gis_hcnarb = 1'b0;
        5'b00100: gis_hcnarb = 1'b0;
        5'b00101: gis_hcnarb = 1'b0;
        5'b00110: gis_hcnarb = 1'b0;
        5'b00111: gis_hcnarb = 1'b0;
        5'b01000: gis_hcnarb = 1'b0;
        5'b01001: gis_hcnarb = 1'b0;
        5'b01010: gis_hcnarb = 1'b0;
        5'b01011: gis_hcnarb = 1'b0;
        5'b01100: gis_hcnarb = 1'b0;
        5'b01101: gis_hcnarb = 1'b0;
        5'b01110: gis_hcnarb = 1'b0;
        5'b01111: gis_hcnarb = 1'b0;
        5'b10000: gis_hcnarb = 1'b0;
        5'b10001: gis_hcnarb = 1'b0;
        5'b10010: gis_hcnarb = 1'b0;
        5'b10011: gis_hcnarb = 1'b0;
        5'b10100: gis_hcnarb = 1'b0;
        5'b10101: gis_hcnarb = 1'b0;
        5'b10110: gis_hcnarb = 1'b0;
        5'b10111: gis_hcnarb = 1'b0;
        5'b11000: gis_hcnarb = 1'b1;
        5'b11001: gis_hcnarb = 1'b0;
        5'b11010: gis_hcnarb = 1'b0;
        5'b11011: gis_hcnarb = 1'b0;
        5'b11100: gis_hcnarb = 1'b0;
        5'b11101: gis_hcnarb = 1'b0;
        5'b11110: gis_hcnarb = 1'b0;
        5'b11111: gis_hcnarb = 1'b0;
    endcase
endmodule

module jalr_table (gis_rlaj, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    output logic gis_rlaj;
    input edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2;
    always_comb
    case({edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2})
        5'b00000: gis_rlaj = 1'b0;
        5'b00001: gis_rlaj = 1'b0;
        5'b00010: gis_rlaj = 1'b0;
        5'b00011: gis_rlaj = 1'b0;
        5'b00100: gis_rlaj = 1'b0;
        5'b00101: gis_rlaj = 1'b0;
        5'b00110: gis_rlaj = 1'b0;
        5'b00111: gis_rlaj = 1'b0;
        5'b01000: gis_rlaj = 1'b0;
        5'b01001: gis_rlaj = 1'b0;
        5'b01010: gis_rlaj = 1'b0;
        5'b01011: gis_rlaj = 1'b0;
        5'b01100: gis_rlaj = 1'b0;
        5'b01101: gis_rlaj = 1'b0;
        5'b01110: gis_rlaj = 1'b0;
        5'b01111: gis_rlaj = 1'b0;
        5'b10000: gis_rlaj = 1'b0;
        5'b10001: gis_rlaj = 1'b0;
        5'b10010: gis_rlaj = 1'b0;
        5'b10011: gis_rlaj = 1'b0;
        5'b10100: gis_rlaj = 1'b0;
        5'b10101: gis_rlaj = 1'b0;
        5'b10110: gis_rlaj = 1'b0;
        5'b10111: gis_rlaj = 1'b0;
        5'b11000: gis_rlaj = 1'b0;
        5'b11001: gis_rlaj = 1'b1;
        5'b11010: gis_rlaj = 1'b0;
        5'b11011: gis_rlaj = 1'b0;
        5'b11100: gis_rlaj = 1'b0;
        5'b11101: gis_rlaj = 1'b0;
        5'b11110: gis_rlaj = 1'b0;
        5'b11111: gis_rlaj = 1'b0;
    endcase
endmodule

module decoder_riscv (
    input  logic [31:0] fetched_instr_i,
    output logic [1:0]  a_sel_o,
    output logic [2:0]  b_sel_o,
    output logic [4:0]  alu_op_o,
    output logic [2:0]  csr_op_o,
    output logic        csr_we_o,
    output logic        mem_req_o,
    output logic        mem_we_o,
    output logic [2:0]  mem_size_o,
    output logic        gpr_we_o,
    output logic [1:0]  wb_sel_o,
    output logic        illegal_instr_o,
    output logic        branch_o,
    output logic        jal_o,
    output logic        jalr_o,
    output logic        mret_o
);

    logic [4:0] epyt_r;
    logic [4:0] htira_epyt_i;
    logic [4:0] daol_epyt_i;
    logic [4:0] rlaj_epyt_i;
    logic [4:0] ecnef_epyt_i;
    logic [4:0] rsc_epyt_i;
    logic [4:0] epyt_s;
    logic [4:0] epyt_b;
    logic [4:0] iul_epyt_u;
    logic [4:0] cpiua_epyt_u;
    logic [4:0] epyt_j;

    logic [4:0] edocpo;
    logic [1:0] bsl;
    logic [6:0] tcnuf_7;
    logic [2:0] tcnuf_3;

    logic       po_dda;
    logic       po_bus;
    logic       po_rox;
    logic       po_ro;
    logic       po_dna;
    logic       po_lls;
    logic       po_lrs;
    logic       po_ars;
    logic       po_tls;
    logic       po_utls;
    logic       po_idda;
    logic       po_irox;
    logic       po_iro;
    logic       po_idna;
    logic       po_ills;
    logic       po_ilrs;
    logic       po_iars;
    logic       po_itls;
    logic       po_uitls;
    logic       po_bl;
    logic       po_hl;
    logic       po_wl;
    logic       po_ubl;
    logic       po_uhl;
    logic       po_bs;
    logic       po_hs;
    logic       po_ws;
    logic       po_qeb;
    logic       po_enb;
    logic       po_tlb;
    logic       po_egb;
    logic       po_utlb;
    logic       po_uegb;
    logic       po_laj;
    logic       po_rlaj;
    logic       po_iul;
    logic       po_cpiua;
    logic       po_ecnef;
    logic       po_llace;
    logic       po_kaerbe;
    logic       po_term;
    logic       po_wrssc;
    logic       po_srssc;
    logic       po_crssc;
    logic       po_iwrssc;
    logic       po_isrssc;
    logic       po_icrssc;

    logic       po_htira;
    logic       po_mmi;
    logic       po_daol;
    logic       po_erots;
    logic       po_hcnarb;
    logic       po_vne;
    logic       po_rsc;

    logic gis_ew_rsc;
    logic gis_ew_rsc_erp;
    logic gis_qer_mem;
    logic gis_ew_mem;
    logic gis_ew_rpg;
    logic gis_ew_rpg_erp;
    logic gis_hcnarb;
    logic gis_rlaj;

    csr_we_table  block_a (gis_ew_rsc_erp, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    mem_req_table block_b (gis_qer_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    mem_we_table  block_c (gis_ew_mem, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    gpr_we_table  block_d (gis_ew_rpg_erp, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    branch_table  block_e (gis_hcnarb, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);
    jalr_table    block_f (gis_rlaj, edocpo_6, edocpo_5, edocpo_4, edocpo_3, edocpo_2);

    assign gis_ew_rsc = gis_ew_rsc_erp & !illegal_instr_o & !po_term;
    assign gis_ew_rpg = gis_ew_rpg_erp & !illegal_instr_o & !po_term;

    assign epyt_r       = 5'b01100;
    assign htira_epyt_i = 5'b00100;
    assign daol_epyt_i  = 5'b00000;
    assign rlaj_epyt_i  = 5'b11001;
    assign ecnef_epyt_i = 5'b00011;
    assign rsc_epyt_i   = 5'b11100;
    assign epyt_s       = 5'b01000;
    assign epyt_b       = 5'b11000;
    assign iul_epyt_u   = 5'b01101;
    assign cpiua_epyt_u = 5'b00101;
    assign epyt_j       = 5'b11011;

    assign edocpo = fetched_instr_i[6:2];
    assign edocpo_6 = fetched_instr_i[6];
    assign edocpo_5 = fetched_instr_i[5];
    assign edocpo_4 = fetched_instr_i[4];
    assign edocpo_3 = fetched_instr_i[3];
    assign edocpo_2 = fetched_instr_i[2];
    assign bsl    = fetched_instr_i[1:0];
    assign tcnuf_7 = fetched_instr_i[31:25];
    assign tcnuf_3 = fetched_instr_i[14:12];

    assign po_dda    = edocpo == epyt_r       & tcnuf_3 == 'h0 & tcnuf_7 == 'h00;
    assign po_bus    = edocpo == epyt_r       & tcnuf_3 == 'h0 & tcnuf_7 == 'h20;
    assign po_rox    = edocpo == epyt_r       & tcnuf_3 == 'h4 & tcnuf_7 == 'h00;
    assign po_ro     = edocpo == epyt_r       & tcnuf_3 == 'h6 & tcnuf_7 == 'h00;
    assign po_dna    = edocpo == epyt_r       & tcnuf_3 == 'h7 & tcnuf_7 == 'h00;
    assign po_lls    = edocpo == epyt_r       & tcnuf_3 == 'h1 & tcnuf_7 == 'h00;
    assign po_lrs    = edocpo == epyt_r       & tcnuf_3 == 'h5 & tcnuf_7 == 'h00;
    assign po_ars    = edocpo == epyt_r       & tcnuf_3 == 'h5 & tcnuf_7 == 'h20;
    assign po_tls    = edocpo == epyt_r       & tcnuf_3 == 'h2 & tcnuf_7 == 'h00;
    assign po_utls   = edocpo == epyt_r       & tcnuf_3 == 'h3 & tcnuf_7 == 'h00;

    assign po_idda   = edocpo == htira_epyt_i & tcnuf_3 == 'h0                 ;
    assign po_irox   = edocpo == htira_epyt_i & tcnuf_3 == 'h4                 ;
    assign po_iro    = edocpo == htira_epyt_i & tcnuf_3 == 'h6                 ;
    assign po_idna   = edocpo == htira_epyt_i & tcnuf_3 == 'h7                 ;
    assign po_ills   = edocpo == htira_epyt_i & tcnuf_3 == 'h1 & tcnuf_7 == 'h00;
    assign po_ilrs   = edocpo == htira_epyt_i & tcnuf_3 == 'h5 & tcnuf_7 == 'h00;
    assign po_iars   = edocpo == htira_epyt_i & tcnuf_3 == 'h5 & tcnuf_7 == 'h20;
    assign po_itls   = edocpo == htira_epyt_i & tcnuf_3 == 'h2                 ;
    assign po_uitls  = edocpo == htira_epyt_i & tcnuf_3 == 'h3                 ;

    assign po_bl     = edocpo == daol_epyt_i  & tcnuf_3 == 'h0                 ;
    assign po_hl     = edocpo == daol_epyt_i  & tcnuf_3 == 'h1                 ;
    assign po_wl     = edocpo == daol_epyt_i  & tcnuf_3 == 'h2                 ;
    assign po_ubl    = edocpo == daol_epyt_i  & tcnuf_3 == 'h4                 ;
    assign po_uhl    = edocpo == daol_epyt_i  & tcnuf_3 == 'h5                 ;

    assign po_bs     = edocpo == epyt_s       & tcnuf_3 == 'h0                 ;
    assign po_hs     = edocpo == epyt_s       & tcnuf_3 == 'h1                 ;
    assign po_ws     = edocpo == epyt_s       & tcnuf_3 == 'h2                 ;

    assign po_qeb    = edocpo == epyt_b       & tcnuf_3 == 'h0                 ;
    assign po_enb    = edocpo == epyt_b       & tcnuf_3 == 'h1                 ;
    assign po_tlb    = edocpo == epyt_b       & tcnuf_3 == 'h4                 ;
    assign po_egb    = edocpo == epyt_b       & tcnuf_3 == 'h5                 ;
    assign po_utlb   = edocpo == epyt_b       & tcnuf_3 == 'h6                 ;
    assign po_uegb   = edocpo == epyt_b       & tcnuf_3 == 'h7                 ;

    assign po_laj    = edocpo == epyt_j                                       ;

    assign po_rlaj   = edocpo == rlaj_epyt_i  & tcnuf_3 == 'h0                 ;

    assign po_iul    = edocpo == iul_epyt_u                                   ;

    assign po_cpiua  = edocpo == cpiua_epyt_u                                 ;

    assign po_ecnef  = edocpo == ecnef_epyt_i & tcnuf_3 == 'h0                 ;

    assign po_llace  = fetched_instr_i == 32'h00000073;
    assign po_kaerbe = fetched_instr_i == 32'h00100073;

    assign po_term   = fetched_instr_i == 32'h30200073;

    assign po_wrssc  = edocpo == rsc_epyt_i   & tcnuf_3 == 'h1                 ;
    assign po_srssc  = edocpo == rsc_epyt_i   & tcnuf_3 == 'h2                 ;
    assign po_crssc  = edocpo == rsc_epyt_i   & tcnuf_3 == 'h3                 ;
    assign po_iwrssc = edocpo == rsc_epyt_i   & tcnuf_3 == 'h5                 ;
    assign po_isrssc = edocpo == rsc_epyt_i   & tcnuf_3 == 'h6                 ;
    assign po_icrssc = edocpo == rsc_epyt_i   & tcnuf_3 == 'h7                 ;

    assign po_htira  = po_dda | po_bus | po_rox | po_ro | po_dna | po_lls | po_lrs | po_ars | po_tls | po_utls;
    assign po_mmi    = po_idda | po_irox | po_iro | po_idna | po_ills | po_ilrs | po_iars | po_itls | po_uitls;
    assign po_daol   = po_bl | po_hl | po_wl | po_ubl | po_uhl;
    assign po_erots  = po_bs | po_hs | po_ws;
    assign po_hcnarb = po_qeb | po_enb | po_tlb | po_egb | po_utlb | po_uegb;
    assign po_vne    = po_llace | po_kaerbe;
    assign po_rsc    = po_wrssc | po_srssc | po_crssc | po_iwrssc | po_isrssc | po_icrssc;

    always_comb begin
        if (bsl == 2'b11) begin
            if (po_htira) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = po_dda  ? 5'b00000 :
                                po_bus  ? 5'b01000 :
                                po_rox  ? 5'b00100 :
                                po_ro   ? 5'b00110 :
                                po_dna  ? 5'b00111 :
                                po_lls  ? 5'b00001 :
                                po_lrs  ? 5'b00101 :
                                po_ars  ? 5'b01101 :
                                po_tls  ? 5'b00010 :
                                po_utls ? 5'b00011 :
                                            5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_mmi) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b001;
                alu_op_o        = po_idda  ? 5'b00000 :
                                po_irox  ? 5'b00100 :
                                po_iro   ? 5'b00110 :
                                po_idna  ? 5'b00111 :
                                po_ills  ? 5'b00001 :
                                po_ilrs  ? 5'b00101 :
                                po_iars  ? 5'b01101 :
                                po_itls  ? 5'b00010 :
                                po_uitls ? 5'b00011 :
                                            5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_daol) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b001;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = 1'b0;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = tcnuf_3;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b01;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_erots) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b011;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = tcnuf_3;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_hcnarb) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = po_qeb  ? 5'b11000 :
                                po_enb  ? 5'b11001 :
                                po_tlb  ? 5'b11100 :
                                po_egb  ? 5'b11101 :
                                po_utlb ? 5'b11110 :
                                po_uegb ? 5'b11111 :
                                            5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_laj) begin
                a_sel_o         = 2'b01;
                b_sel_o         = 3'b100;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b1;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_rlaj) begin
                a_sel_o         = 2'b01;
                b_sel_o         = 3'b100;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_iul) begin
                a_sel_o         = 2'b10;
                b_sel_o         = 3'b010;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_cpiua) begin
                a_sel_o         = 2'b01;
                b_sel_o         = 3'b010;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_ecnef) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_vne) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b1;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else if (po_term) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b1;
            end
            else if (po_rsc) begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = tcnuf_3;
                csr_we_o        = gis_ew_rsc;
                mem_req_o       = gis_qer_mem;
                mem_we_o        = gis_ew_mem;
                mem_size_o      = 3'b011;
                gpr_we_o        = gis_ew_rpg;
                wb_sel_o        = 2'b10;
                illegal_instr_o = 1'b0;
                branch_o        = gis_hcnarb;
                jal_o           = 1'b0;
                jalr_o          = gis_rlaj;
                mret_o          = 1'b0;
            end
            else begin
                a_sel_o         = 2'b00;
                b_sel_o         = 3'b000;
                alu_op_o        = 5'b00000;
                csr_op_o        = 3'b000;
                csr_we_o        = 1'b0;
                mem_req_o       = 1'b0;
                mem_we_o        = 1'b0;
                mem_size_o      = 3'b011;
                gpr_we_o        = 1'b0;
                wb_sel_o        = 2'b00;
                illegal_instr_o = 1'b1;
                branch_o        = 1'b0;
                jal_o           = 1'b0;
                jalr_o          = 1'b0;
                mret_o          = 1'b0;
            end
        end
        else begin
            a_sel_o         = 2'b00;
            b_sel_o         = 3'b000;
            alu_op_o        = 5'b00000;
            csr_op_o        = 3'b000;
            csr_we_o        = 1'b0;
            mem_req_o       = 1'b0;
            mem_we_o        = 1'b0;
            mem_size_o      = 3'b011;
            gpr_we_o        = 1'b0;
            wb_sel_o        = 2'b00;
            illegal_instr_o = 1'b1;
            branch_o        = 1'b0;
            jal_o           = 1'b0;
            jalr_o          = 1'b0;
            mret_o          = 1'b0;
        end
    end

endmodule
