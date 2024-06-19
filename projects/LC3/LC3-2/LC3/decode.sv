module decode(
    input             clk,
    input             rst,
    input             enable_decode,
    input      [15:0] Instr_dout,
    input      [15:0] npc_in,
    output reg [15:0] IR,
    output reg [5:0]  E_Control,
    output reg [1:0]  W_Control,
    output reg        Mem_Control,
    output reg [15:0] npc_out
    );
    
    control_decode cntrl_d(
        .clk(clk),
        .rst(rst),
        .enable_decode(enable_decode),
        .Instr_dout(Instr_dout),
        .E_Control(E_Control),
        .W_Control(W_Control),
        .Mem_Control(Mem_Control)
    );
    
    always @(posedge clk) begin
        if (rst) begin
            IR      <= 16'h5020;  // AND R0, R0, #0 is the NOP instruction in this project
            npc_out <= 16'h0;
        end else begin
            if (enable_decode) begin
                IR <= Instr_dout;
                npc_out <= npc_in;
            end
        end
    end   
endmodule

///////////////////////////////////////////////

interface decode_if;
    logic        clk;
    logic        rst;
    logic        enable_decode;
    logic [15:0] Instr_dout;
    logic [15:0] npc_in;
    logic [15:0] IR;
    logic [5:0]  E_Control;
    logic [1:0]  W_Control;
    logic        Mem_Control;
    logic [15:0] npc_out;
endinterface