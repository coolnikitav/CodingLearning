module memaccess(
    input  [1:0]  mem_state,
    input         M_Control,
    input  [15:0] M_Data,
    input  [15:0] M_Addr,  
    input  [15:0] DMem_dout,
    output [15:0] DMem_addr,
    output        DMem_rd,
    output [15:0] DMem_din,
    output [15:0] memout
    );
    localparam READ_MEM = 2'h0,
               READ_MEM_INDIR = 2'h1,
               WRITE_MEM = 2'h2,
               INIT_STATE = 2'h3;
    
    reg [15:0] DMem_addr_reg, 
               DMem_rd_reg, 
               DMem_din_reg, 
               memout_reg;
                
    always @ (*) begin
        case (mem_state)
            READ_MEM: begin
                if (M_Control) begin
                    DMem_addr_reg <= DMem_dout;  // Indirect addressing
                end else begin
                    DMem_addr_reg <= M_Addr;     // Direct addressing
                end
                DMem_din_reg <= 16'b0;
                DMem_rd_reg  <= 1'b1;
                memout_reg   <= DMem_dout;
            end
            READ_MEM_INDIR: begin
                DMem_addr_reg <= M_Addr;
                DMem_din_reg  <= 16'b0;
                DMem_rd_reg   <= 1'b1;
                memout_reg    <=  DMem_dout;
            end
            WRITE_MEM: begin
                if (M_Control) begin
                    DMem_addr_reg <= DMem_dout;  // Indirect addressing
                end else begin
                    DMem_addr_reg <= M_Addr;     // Direct addressing
                end
                DMem_din_reg <= M_Data;
                DMem_rd_reg  <= 1'b0;
                memout_reg   <= DMem_dout;
            end
            INIT_STATE: begin
                DMem_addr_reg <= 16'bz;
                DMem_din_reg  <= 16'bz;
                DMem_rd_reg   <= 1'bz;
                memout_reg    <= DMem_dout;
            end
        endcase
    end
    
    /*
     *  Output assignment
     */
    assign DMem_addr = DMem_addr_reg;
    assign DMem_rd   = DMem_rd_reg;
    assign DMem_din  = DMem_din_reg; 
    assign memout    = memout_reg;
endmodule

///////////////////////////////////////////////

interface memaccess_if;
    logic [1:0]  mem_state;
    logic        M_Control;
    logic [15:0] M_Data;
    logic [15:0] M_Addr;  
    logic [15:0] DMem_dout;
    logic [15:0] DMem_addr;
    logic        DMem_rd;
    logic [15:0] DMem_din;
    logic [15:0] memout; 
endinterface