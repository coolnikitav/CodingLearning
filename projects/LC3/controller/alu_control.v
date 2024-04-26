module alu(
    input             clk,
    input             rst,
    input             enable,
    input      [1:0]  alu_control,
    input      [15:0] aluin1,
    input      [15:0] aluin2,
    output reg [15:0] aluout
    );
    
    always @ (posedge clk) begin
        if (rst == 1'b1) begin
            aluout <= 16'h0;
        end else if (enable == 1'b1) begin
            case (alu_control)
                2'h0: aluout <= aluin1 + aluin2;
                2'h1: aluout <= aluin1 & aluin2;
                2'h2: aluout <= ~aluin1;
            endcase
        end
    end
endmodule
