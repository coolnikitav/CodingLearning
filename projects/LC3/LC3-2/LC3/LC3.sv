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
wire        enable_updatePC;
wire        enable_fetch;
wire        enable_decode;
wire        enable_execute;
wire        enable_writeback;

wire        bypass_alu_1;
wire        bypass_alu_2;
wire        bypass_mem_1;
wire        bypass_mem_2;

wire [5:0]  E_Control;
wire [1:0]  W_Control;
wire        Mem_Control;

wire [1:0]  W_Control_out;
wire        Mem_Control_out;

wire [15:0] IR;
wire [15:0] IR_Exec;

wire [15:0] npc_f;
wire [15:0] npc_d;

wire [2:0]  dr;
wire [2:0]  sr1;
wire [2:0]  sr2;

wire [15:0] VSR1;
wire [15:0] VSR2;

wire        br_taken;
wire [2:0]  psr;
wire [2:0]  NZP;

wire [1:0]  mem_state;

wire [15:0] aluout;
wire [15:0] pcout;
wire [15:0] memout;

wire [15:0] M_Data;

fetch f(
    .clk(clk), 
    .rst(rst),
    .enable_updatePC(enable_updatePC),
    .enable_fetch(enable_fetch),
    .taddr(pcout),
    .br_taken(br_taken),
    .pc(PC),
    .npc(npc_f),
    .Imem_rd(instrmem_rd)
);

decode d(
    .clk(clk),
    .rst(rst),
    .enable_decode(enable_decode),
    .Instr_dout(Instr_dout),
    .npc_in(npc_f),
    .IR(IR),
    .E_Control(E_Control),
    .W_Control(W_Control),
    .Mem_Control(Mem_Control),
    .npc_out(npc_d)
);

execute e(
    .clk(clk),
    .rst(rst),
    .enable_execute(enable_execute),
    .E_Control_in(E_Control),
    .W_Control_in(W_Control),
    .Mem_Control_in(Mem_Control),
    .bypass_alu_1(bypass_alu_1),
    .bypass_alu_2(bypass_alu_2),
    .bypass_mem_1(bypass_mem_1),
    .bypass_mem_2(bypass_mem_2),
    .IR(IR),
    .npc_in(npc_d),
    .Mem_Bypass_val(memout),
    .aluout(aluout),
    .W_Control_out(W_Control_out),
    .Mem_Control_out(Mem_Control_out),
    .M_Data(M_Data),
    .VSR1(VSR1),
    .VSR2(VSR2),
    .dr(dr),
    .sr1(sr1),
    .sr2(sr2),
    .pcout(pcout),
    .NZP(NZP),
    .IR_Exec(IR_Exec)
);

writeback w(
    .clk(clk),
    .rst(rst),
    .enable_writeback(enable_writeback),
    .aluout(aluout),        
    .memout(memout),
    .pcout(pcout),
    .W_Control(W_Control_out),
    .VSR1(VSR1),
    .VSR2(VSR2),
    .dr(dr),
    .sr1(sr1),
    .sr2(sr2),
    .psr(psr)
);

memaccess m(
    .mem_state(mem_state),
    .M_Control(Mem_Control_out),
    .M_Data(M_Data),
    .M_Addr(pcout),  
    .DMem_dout(Data_dout),
    .DMem_addr(Data_addr),
    .DMem_rd(Data_rd),
    .DMem_din(Data_din),
    .memout(memout)
);

controller c(
    .clk(clk),
    .rst(rst),
    .complete_data(complete_data),
    .complete_instr(complete_instr),
    .IR(IR),
    .NZP(NZP),
    .psr(psr),
    .IR_Exec(IR_Exec),
    .IMem_dout(Instr_dout),
    .enable_updatePC(enable_updatePC),
    .enable_fetch(enable_fetch),
    .enable_decode(enable_decode),
    .enable_execute(enable_execute),
    .enable_writeback(enable_writeback),
    .br_taken(br_taken),
    .bypass_alu_1(bypass_alu_1),
    .bypass_alu_2(bypass_alu_2),
    .bypass_mem_1(bypass_mem_1),
    .bypass_mem_2(bypass_mem_2),
    .mem_state(mem_state)
);
endmodule

///////////////////////////////////////////////

interface LC3_if;
    logic        clk;
    logic        rst;
    logic        complete_data;
    logic        complete_instr;
    logic [15:0] Instr_dout;
    logic [15:0] Data_dout;
    logic [15:0] PC;
    logic        instrmem_rd;
    logic        Data_addr;
    logic        Data_din;
    logic        Data_rd;
endinterface
