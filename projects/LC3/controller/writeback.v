module writeback(
    input         clk,
    input         rst,
    input         enable_writeback,
    input  [15:0] aluout,
    input  [1:0]  W_Control,
    input  [15:0] pcout,
    input  [15:0] memout,
    output [15:0] VSR1,
    output [15:0] VSR2,
    input  [2:0]  dr,
    input  [2:0]  sr1,
    input  [2:0]  sr2
    );
    
    reg_file rf(
        .clk(clk),
        .rst(rst),
        .en(enable_writeback),
        .dr(dr),
        .sr1(sr1),
        .sr2(sr2),
        .DR_in(DR_in),
        .VSR1(VSR1),
        .VSR2(VSR2)
    );
    
    reg [15:0] DR_in;
    
    always @ (*) begin
        case (W_Control)
            2'h0: DR_in = aluout;           
            2'h1: DR_in = memout;            
            2'h2: DR_in = pcout;
        endcase
    end
endmodule
