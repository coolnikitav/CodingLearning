module decode(
    input             clk,
    input             rst,
    input      [15:0] npc_in,
    input             enable_decode,
    input      [15:0] Imem_dout,
    output reg [15:0] IR,
    output reg [15:0] npc_out,
    output reg [1:0]  W_Control,
    output reg [5:0]  E_Control
    );
    
    always @ (posedge clk) begin
        if (rst == 1'b1) begin
            IR <= 16'b0;
            npc_out <= 16'b0;
            W_Control <= 2'b0;
            E_Control <= 6'b0;
        end else begin
            if (enable_decode == 1'b1) begin
                IR <= Imem_dout;
                npc_out <= npc_in;
             
                casex (Imem_dout[15:12])
                    4'b??01: W_Control <= 2'b00;
                    4'b1110: W_Control <= 2'b10;
                endcase
                
                case (Imem_dout[15:12])
                    4'b0001: begin
                        case(Imem_dout[5])
                            0: E_Control <= 6'b000001;
                            1: E_Control <= 6'b000000;
                        endcase
                    end
                    4'b0101: begin
                        case(Imem_dout[5])
                            0: E_Control <= 6'b010001;
                            1: E_Control <= 6'b010000;
                        endcase
                    end
                    4'b1001:   E_Control <= 6'b100000;
                    4'b1110:   E_Control <= 6'b000110;
                endcase
            end
        end
    end
endmodule