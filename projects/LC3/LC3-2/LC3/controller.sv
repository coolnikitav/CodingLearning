module controller(
    input             clk,
    input             rst,
    input             complete_data,
    input             complete_instr,
    input      [15:0] IR,
    input      [2:0]  NZP,
    input      [2:0]  psr,
    input      [15:0] IR_Exec,
    input      [15:0] IMem_dout,
    output reg        enable_updatePC,
    output reg        enable_fetch,
    output reg        enable_decode,
    output reg        enable_execute,
    output reg        enable_writeback,
    output reg        br_taken,
    output reg        bypass_alu_1,
    output reg        bypass_alu_2,
    output reg        bypass_mem_1,
    output reg        bypass_mem_2,
    output reg [2:0]  mem_state
    );   
    typedef enum bit [3:0] {
        // ALU Operations
        ADD_op = 4'b0001,
        AND_op = 4'b0101,
        NOT_op = 4'b1001,        
        
        //Memory Operations
        LD_op  = 4'b0010,
        LDR_op = 4'b0110,
        LDI_op = 4'b1010,
        LEA_op = 4'b1110,
        ST_op  = 4'b0011,
        STR_op = 4'b0111,
        STI_op = 4'b1011,
        
        // Control Operations
        BR_op  = 4'b0000,
        JMP_op = 4'b1100
    } op_t;
    
    /*
     *  Enables
     */
    always @ (posedge clk) begin
        if (rst) begin
            enable_updatePC  <= 1'b0;
            enable_fetch     <= 1'b0;
            enable_decode    <= 1'b0;
            enable_execute   <= 1'b0;
            enable_writeback <= 1'b0;
        end else begin
            enable_updatePC  <= ~(IR[15:12] inside { LD_op, LDR_op, LDI_op, ST_op, STR_op, STI_op } || IMem_dout[15:12] inside { BR_op, JMP_op });
            enable_fetch     <= ~(IR[15:12] inside { LD_op, LDR_op, LDI_op, ST_op, STR_op, STI_op } || IMem_dout[15:12] inside { BR_op, JMP_op });
            enable_decode    <= (IR[15:12] inside { LD_op, LDR_op, LDI_op, ST_op, STR_op, STI_op }) ? 1'b0 : enable_fetch;
            enable_execute   <= (IR[15:12] inside { LD_op, LDR_op, LDI_op, ST_op, STR_op, STI_op }) ? 1'b0 : enable_decode;
            enable_writeback <= (IR[15:12] inside { LD_op, LDR_op, LDI_op, ST_op, STR_op, STI_op }) ? 1'b0 : enable_execute;
        end
    end 
    
    /*
     *  br_taken
     */
    always @ (posedge clk) begin
        if (rst) begin
            br_taken <= 1'b0;
        end else begin
            br_taken <= | (NZP & psr);
        end
    end 
    
    /*
     *  Bypass
     */
    always @ (posedge clk) begin
        if (rst) begin
            bypass_alu_1 <= 1'b0;
            bypass_alu_2 <= 1'b0;
            bypass_mem_1 <= 1'b0;
            bypass_mem_2 <= 1'b0;
        end else begin
            if (IR[15:12] inside { ADD_op, AND_op, NOT_op }) begin
                if (IR_Exec[15:12] inside { ADD_op, AND_op, NOT_op }) begin
                    bypass_alu_1 <= IR[8:6] == IR_Exec[11:9];
                    bypass_alu_2 <= IR[2:0] == IR_Exec[11:9] && ~IR[5];        // only ADD, AND register op
                end else if (IR_Exec[15:12] inside { LD_op, LDR_op, LDI_op, LEA_op }) begin
                    bypass_mem_1 <= IR[8:6] == IR_Exec[11:9];
                    bypass_mem_2 <= IR[2:0] == IR_Exec[11:9] && ~IR[5];  // only ADD, AND register op
                end  
            end else if (IR[15:12] inside { ST_op, STI_op }) begin
                if (IR_Exec[15:12] inside { ADD_op, AND_op, NOT_op }) begin
                    bypass_alu_2 <= IR[11:9] == IR_Exec[11:9];
                end else if (IR_Exec[15:12] inside { LD_op, LDR_op, LDI_op, LEA_op }) begin
                    bypass_mem_2 <= IR[11:9] == IR_Exec[11:9] && ~IR[5];
                end
            end else if (IR[15:12] inside { STR_op }) begin
                if (IR_Exec[15:12] inside { ADD_op, AND_op, NOT_op }) begin
                    bypass_alu_1 <= IR[8:6]  == IR_Exec[11:9];
                    bypass_alu_2 <= IR[11:9] == IR_Exec;
                end else if (IR_Exec[15:12] inside { LD_op, LDR_op, LDI_op, LEA_op }) begin
                    bypass_mem_1 <= IR[8:6]  == IR_Exec[11:9];
                    bypass_mem_2 <= IR[11:9] == IR_Exec[11:9];
                end 
            end else begin
                bypass_alu_1 <= 1'b0;
                bypass_alu_2 <= 1'b0;
                bypass_mem_1 <= 1'b0;
                bypass_mem_2 <= 1'b0;
            end          
        end
    end 
     
    /*
     *  mem_state
     */
    always @ (posedge clk) begin
        if (rst) begin
            mem_state <= 2'h3;
        end else begin
            if (IR_Exec[15:12] inside { LD_op, LDR_op }) begin
                mem_state <= 2'h0;
            end else if (IR_Exec[15:12] inside { LDI_op, STI_op }) begin
                mem_state <= 2'h1;
            end else if (IR_Exec[15:12] inside { ST_op, STR_op }) begin
                mem_state <= 2'h2;
            end else begin
                mem_state <= 2'h3;
            end
        end
    end 
endmodule

///////////////////////////////////////////////

interface controller_if;
    logic        clk;
    logic        rst;
    logic        complete_data;
    logic        complete_instr;
    logic [15:0] IR;
    logic [2:0]  NZP;
    logic [2:0]  psr;
    logic [15:0] IR_Exec;
    logic [15:0] IMem_dout;
    logic        enable_updatePC;
    logic        enable_fetch;
    logic        enable_decode;
    logic        enable_execute;
    logic        enable_writeback;
    logic        br_taken;
    logic        bypass_alu_1;
    logic        bypass_alu_2;
    logic        bypass_mem_1;
    logic        bypass_mem_2;
    logic [2:0]  mem_state;
endinterface