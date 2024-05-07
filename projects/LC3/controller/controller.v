module controller(
    input        clk,
    input        rst,
    input        enable_updatePC,
    input        enable_fetch,
    input [15:0] taddr,
    input        br_taken,
    input        enable_decode,
    input [15:0] Imem_dout,
    input        enable_execute,
    input        enable_writeback,
    input [15:0] memout
    );
    
    wire [15:0] pc_f;
    wire [15:0] npc_f_to_d;
    wire        Imem_rd_f;
     
    fetch f(
        .clk(clk), 
        .rst(rst),
        .enable_updatePC(enable_updatePC),
        .enable_fetch(enable_fetch),
        .taddr(taddr),
        .br_taken(br_taken),
        .pc(pc_f),
        .npc(npc_f_to_d),
        .Imem_rd(Imem_rd_f)
    );
    
    wire [15:0] IR_d_to_e;
    wire [15:0] npc_d_to_e;
    wire [1:0]  W_Control_d_to_e;
    wire [5:0]  E_Control_d_to_e;
    
    decode d(
        .clk(clk),
        .rst(rst),
        .npc_in(npc_f_to_d),
        .enable_decode(enable_decode),
        .Imem_dout(Imem_dout),
        .IR(IR_d_to_e),
        .npc_out(npc_d_to_e),
        .W_Control(W_Control_d_to_e),
        .E_Control(E_Control_d_to_e)
    );
    
    wire [15:0] aluout_e_to_w;
    wire [1:0]  W_Control_e_to_w;
    wire [15:0] VSR1_w_to_e;
    wire [15:0] VSR2_w_to_e;
    wire [2:0]  dr_e_to_w;
    wire [2:0]  sr1_e_to_w;
    wire [2:0]  sr2_e_to_w;
    wire [15:0] pcout_e_to_w;
    
    execute e(
        .clk(clk),
        .rst(rst),
        .enable_execute(enable_execute),
        .E_control(E_Control_d_to_e),
        .IR(IR_d_to_e),
        .npc_in(npc_d_to_e),
        .W_control_in(W_Control_d_to_e),
        .aluout(aluout_e_to_w),
        .W_control_out(W_Control_e_to_w),
        .VSR1(VSR1_w_to_e),
        .VSR2(VSR2_w_to_e),
        .dr(dr_e_to_w),
        .sr1(sr1_e_to_w),
        .sr2(sr2_e_to_w),
        .pcout(pcout_e_to_w)
    );
    
    writeback w(
        .clk(clk),
        .rst(rst),
        .enable_writeback(enable_writeback),
        .aluout(aluout_e_to_w),
        .W_Control(W_Control_e_to_w),
        .pcout(pcout_e_to_w),
        .memout(memout),
        .VSR1(VSR1_w_to_e),
        .VSR2(VSR2_w_to_e),
        .dr(dr_e_to_w),
        .sr1(sr1_e_to_w),
        .sr2(sr2_e_to_w)
    );
endmodule
