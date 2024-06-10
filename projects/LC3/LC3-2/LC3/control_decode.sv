module control_decode(
    input         clk,
    input         rst,
    input         enable_decode,
    input  [15:0] Instr_dout,
    output [5:0]  E_Control,
    output [1:0]  W_Control,
    output        Mem_Control
    );
    reg [5:0] E_Control_reg;
    reg [1:0] W_Control_reg;
    reg       Mem_Control_reg;
    
    always @(posedge clk) begin
        if (rst) begin
            E_Control_reg   = 6'h0;
            W_Control_reg   = 2'h0;
            Mem_Control_reg = 1'h0; 
        end     
    end
    
    always @(posedge clk) begin
        if (~rst && enable_decode) begin
            case(Instr_dout[15:12])
                4'b0001: E_Control_reg <= Instr_dout[5] == 1'b1 ? 6'b000000 : 6'b000001;  // ADD
                4'b0101: E_Control_reg <= Instr_dout[5] == 1'b1 ? 6'b010000 : 6'b010001;  // AND
                4'b1001: E_Control_reg <= 6'b100000;  // NOT
                4'b0000: E_Control_reg <= 6'b000110;  // BR
                4'b1100: E_Control_reg <= 6'b001100;  // JMP
                4'b0010: E_Control_reg <= 6'b000110;  // LD
                4'b0110: E_Control_reg <= 6'b001000;  // LDR
                4'b1010: E_Control_reg <= 6'b000110;  // LDI
                4'b1110: E_Control_reg <= 6'b000110;  // LEA
                4'b0011: E_Control_reg <= 6'b000110;  // ST
                4'b0111: E_Control_reg <= 6'b001000;  // STR
                4'b1011: E_Control_reg <= 6'b000110;  // STI     
            endcase
        end
    end
    
    always @(posedge clk) begin
        if (~rst && enable_decode) begin
            case(Instr_dout[15:12])
                4'b0001: W_Control_reg <= 2'h0;  // ADD
                4'b0101: W_Control_reg <= 2'h0;  // AND
                4'b1001: W_Control_reg <= 2'h0;  // NOT
                4'b0000: W_Control_reg <= 2'h0;  // BR
                4'b1100: W_Control_reg <= 2'h0;  // JMP
                4'b0010: W_Control_reg <= 2'h1;  // LD
                4'b0110: W_Control_reg <= 2'h1;  // LDR
                4'b1010: W_Control_reg <= 2'h1;  // LDI
                4'b1110: W_Control_reg <= 2'h2;  // LEA
                4'b0011: W_Control_reg <= 2'h0;  // ST
                4'b0111: W_Control_reg <= 2'h0;  // STR
                4'b1011: W_Control_reg <= 2'h0;  // STI     
            endcase
        end     
    end
    
    always @(posedge clk) begin
        if (~rst && enable_decode) begin
            case(Instr_dout[15:12])
                4'b0001: Mem_Control_reg <= 1'h0;  // ADD
                4'b0101: Mem_Control_reg <= 1'h0;  // AND
                4'b1001: Mem_Control_reg <= 1'h0;  // NOT
                4'b0000: Mem_Control_reg <= 1'h0;  // BR
                4'b1100: Mem_Control_reg <= 1'h0;  // JMP
                4'b0010: Mem_Control_reg <= 1'h0;  // LD
                4'b0110: Mem_Control_reg <= 1'h0;  // LDR
                4'b1010: Mem_Control_reg <= 1'h1;  // LDI
                4'b1110: Mem_Control_reg <= 1'h0;  // LEA
                4'b0011: Mem_Control_reg <= 1'h0;  // ST
                4'b0111: Mem_Control_reg <= 1'h0;  // STR
                4'b1011: Mem_Control_reg <= 1'h1;  // STI     
            endcase 
        end     
    end
    
    assign E_Control   = E_Control_reg;
    assign W_Control   = W_Control_reg;
    assign Mem_Control = Mem_Control_reg;
endmodule