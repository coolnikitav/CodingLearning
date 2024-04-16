module reg_file(
    input         clk,
    input         en,    
    input  [2:0]  dr,
    input  [2:0]  sr1,
    input  [2:0]  sr2,
    input  [15:0] DR_in,
    output [15:0] VSR1,
    output [15:0] VSR2
    );
    
    reg [15:0] register_files [7:0];
    
    always @ (posedge clk) begin
        if (en == 1'b1) begin
            register_files[dr] <= DR_in;
        end
    end
    
    assign VSR1 = register_files[sr1];
    assign VSR2 = register_files[sr2];
endmodule
