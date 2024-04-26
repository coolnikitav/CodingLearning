module reg_file(
    input         clk,
    input         rst,
    input         en,    
    input  [2:0]  dr,
    input  [2:0]  sr1,
    input  [2:0]  sr2,
    input  [15:0] DR_in,
    output [15:0] VSR1,
    output [15:0] VSR2
    );
    
    reg [15:0] register_files [7:0];
    
    integer i;
    
    always @ (posedge clk) begin
        if (rst == 1'b1) begin
            for (i = 0; i < 8; i=i+1) begin
                register_files[i] <= 16'h0;
            end
        end else if (en == 1'b1) begin
            register_files[dr] <= DR_in;
        end
    end
    
    assign VSR1 = register_files[sr1];
    assign VSR2 = register_files[sr2];
endmodule
