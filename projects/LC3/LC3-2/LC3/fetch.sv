module fetch(
    input         clk, 
    input         rst,
    input         enable_updatePC,
    input         enable_fetch,
    input  [15:0] taddr,
    input         br_taken,
    output [15:0] pc,
    output [15:0] npc,
    output        Imem_rd
    );
    
    /*
     * PC Control
     */
    reg [15:0] pc_reg;
    
    always @ (posedge clk) begin
        if (rst) begin
            pc_reg <= 16'h3000;
        end else begin
            if (enable_updatePC) begin
                if (br_taken) begin
                   pc_reg <= taddr; 
                end else begin
                   pc_reg <= npc;
                end
            end
        end
    end
    
    /*
     * Output Control
     */     
    assign Imem_rd = enable_fetch === 1'b1 ? 1'b1 : 1'bz;  // need === to compare Z values
    assign pc      = pc_reg;
    assign npc     = pc + 1; 
    
endmodule

///////////////////////////////////////////////

interface fetch_if;
    logic        clk, rst;
    logic        enable_updatePC, enable_fetch;
    logic [15:0] taddr;
    logic        br_taken;
    logic [15:0] pc, npc;
    logic        Imem_rd;
endinterface