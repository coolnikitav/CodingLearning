module LC3(
    input         clk,
    input         rst, 
    input         complete_data,
    input         complete_instr,
    input  [15:0] Instr_dout,
    input  [15:0] Data_dout,
    output [15:0] PC,
    output        instrmem_rd,
    output        Data_addr,
    output        Data_din,
    output        Data_rd
);
fetch f(
    .clk, 
    .rst,
    .enable_updatePC,
    .enable_fetch,
    .taddr,
    .br_taken,
    .pc,
    .npc,
    .Imem_rd
);

decode d(
    .clk,
    .rst,
    .enable_decode,
    .Instr_dout,
    .npc_in,
    .IR,
    .E_Control,
    .W_Control,
    .Mem_Control,
    .npc_out
);

execute e(
    .clk,
    .rst,
    .enable_execute,
    .E_Control_in,
    .W_Control_in,
    .Mem_Control_in,
    .bypass_alu_1,
    .bypass_alu_2,
    .bypass_mem_1,
    .bypass_mem_2,
    .IR,
    .npc_in,
    .Mem_Bypass_val,
    .aluout,
    .W_Control_out,
    .Mem_Control_out,
    .M_Data,
    .VSR1,
    .VSR2,
    .dr,
    .sr1,
    .sr2,
    .pcout,
    .NZP,
    .IR_Exec
);

writeback w(
    .clk,
    .rst,
    .enable_writeback,
    .aluout,        
    .memout,
    .pcout,
    .W_Control,
    .VSR1,
    .VSR2,
    .dr,
    .sr1,
    .sr2,
    .psr
);
endmodule