module writeback(
    input         clk,
    input         rst,
    input         enable_writeback,
    input  [15:0] aluout,        
    input  [15:0] memout,
    input  [15:0] pcout,
    input  [1:0]  W_Control,
    output [15:0] VSR1,
    output [15:0] VSR2,
    input  [2:0]  dr,
    input  [2:0]  sr1,
    input  [2:0]  sr2,
    output [2:0]  psr
    );
    
    reg_file RF(
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
    
    /*
     *  DR_in control
     */ 
    reg [15:0] DR_in;
    
    always @ (*) begin
        case (W_Control)
            2'h0: DR_in = aluout;           
            2'h1: DR_in = memout;            
            2'h2: DR_in = pcout;
        endcase
    end
    
    /*
     *   psr control
     */
    reg [2:0] psr_reg;
    
    always @ (posedge clk) begin
        if (rst) begin
            psr_reg <= 3'b0;
        end else begin
            if (!DR_in) begin              // zero
                psr_reg <= 3'b010;
            end else if (DR_in[15]) begin  // negative
                psr_reg <= 3'b100;
            end else begin                 // positive
                psr_reg <= 3'b001; 
            end
        end
    end
    
    assign psr = psr_reg;
endmodule

///////////////////////////////////////////////

interface writeback_if;
    logic        clk;
    logic        rst;
    logic        enable_writeback;
    logic [15:0] aluout;        
    logic [15:0] memout;
    logic [15:0] pcout;
    logic [1:0]  W_Control;
    logic [15:0] VSR1;
    logic [15:0] VSR2;
    logic [2:0]  dr;
    logic [2:0]  sr1;
    logic [2:0]  sr2;
    logic [2:0]  psr;
endinterface