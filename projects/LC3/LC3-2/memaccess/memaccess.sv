module memaccess(
    input  [1:0]  mem_state,
    input         M_Control,
    input  [15:0] M_Data,
    input  [15:0] M_Addr,  
    input  [15:0] DMem_dout,
    output [15:0] DMem_addr,
    output [15:0] DMem_rd,
    output [15:0] DMem_din,
    output [15:0] memout
    );
    assign D_Mem_addr = mem_state == 2'h3 ? 16'hz : M_Addr;
    assign D_Mem_rd   = mem_state == 2'h3 ? 1'hz : (mem_state == 2'h2 ? 1'h0 : 1'h1);
    assign DMem_din   = mem_state == 2'h3 ? 16'hz : M_Data;
    assign memout     = DMem_dout;
endmodule
