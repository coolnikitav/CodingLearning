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
    output reg [1:0]  mem_state
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
    
    wire bubble = (IMem_dout[15:12] === BR_op && IR_Exec[15:12] !== BR_op) || (IMem_dout[15:12] === JMP_op && IR_Exec[15:12] !== JMP_op);
    wire stall  = (IR_Exec[15:12] === LD_op || IR_Exec[15:12] === LDR_op || IR_Exec[15:12] === LDI_op || IR_Exec[15:12] === ST_op || IR_Exec[15:12] ===  STR_op || IR_Exec[15:12] === STI_op) && (mem_state !== 2'h3);
    
    /*
     *  repeated_IR_count is used in br_taken logic
     */
    reg [15:0] prev_IR;
    int repeated_IR_count = 1;
    
    always @ (posedge clk) begin
        prev_IR <= IR;
        if (prev_IR === IR) begin
            repeated_IR_count++;
        end else begin
            repeated_IR_count = 1;
        end
    end
    
    /*
     *  Enables
     */
    always @ (*) begin
        if (rst) begin
            enable_updatePC <= 1'b0;
            enable_fetch    <= 1'b0;
        end else begin
            if (!(stall === 1'b0 && bubble === 1'b0)) begin
                enable_updatePC <= 1'b0;
                enable_fetch    <= 1'b0;
            end else begin
                enable_updatePC <= 1'b1;
            end            
        end
    end
    
    always @ (negedge rst) begin
        enable_updatePC <= 1'b1;
        enable_fetch    <= 1'b1;
    end
    
    always @ (posedge clk) begin
        if (mem_state == 2'h3) begin
            enable_fetch <= enable_updatePC;
        end
    end
    
    always @ (posedge clk) begin
        if (rst) begin
            enable_decode  <= 1'b0;
        end else begin
            enable_decode  <= enable_fetch;
        end
    end
    
    
    always @ (posedge clk) begin
        if (rst) begin
            enable_execute  <= 1'b0;
        end else begin
            enable_execute  <= enable_decode;
        end
    end
    
    always @ (posedge clk) begin
        if (rst) begin
            enable_writeback  <= 1'b0;
        end else begin
            enable_writeback  <= enable_execute;
        end
    end
    
    always @ (*) begin
        if (IR_Exec[15:12] === LD_op || IR_Exec[15:12] === LDR_op || IR_Exec[15:12] === LDI_op || IR_Exec[15:12] === ST_op || IR_Exec[15:12] === STR_op || IR_Exec[15:12] === STI_op) begin  // stall
            enable_updatePC  <= 1'b0;
            enable_fetch     <= 1'b0;
            enable_decode    <= 1'b0;
            enable_execute   <= 1'b0;
            enable_writeback <= 1'b0;
        end else if (IR_Exec[15:12] === BR_op || IR_Exec[15:12] === JMP_op) begin  // control operations don't have writeback
            enable_writeback <= 1'b0;
        end
    end
    
    always @ (posedge clk) begin
        if (mem_state == 0 || mem_state == 2) begin  // enables should go back to 1 after a stall
            enable_updatePC  <= 1'b1;
            enable_fetch     <= 1'b1;
            enable_decode    <= 1'b1;
            enable_execute   <= 1'b1;
        end
        if (mem_state == 0) begin
            enable_writeback <= 1'b1;  // there should be no writeback for stores
        end
    end

    /*
     *  br_taken
     */
    always @ (*) begin
        if (rst) begin
            br_taken <= 1'b0;
        end else begin
            br_taken <= (IR_Exec[15:12] === JMP_op && repeated_IR_count == 1) ? 1'b1 : (| (NZP & psr));  // br_taken needs to go down after branch is taken, so PC can update properly
        end
    end 
    
    /*
     *  Bypass
     */
    always @ (*) begin
        if (rst) begin
            bypass_alu_1 <= 1'b0;
            bypass_alu_2 <= 1'b0;
            bypass_mem_1 <= 1'b0;
            bypass_mem_2 <= 1'b0;
        end else begin
            if (IR[15:12] === ADD_op || IR[15:12] === AND_op || IR[15:12] === NOT_op) begin
                if (IR_Exec[15:12] === ADD_op || IR_Exec[15:12] === AND_op || IR_Exec[15:12] === NOT_op) begin
                    bypass_alu_1 <= IR[8:6] == IR_Exec[11:9];
                    bypass_alu_2 <= IR[2:0] == IR_Exec[11:9] && ~IR[5];        // only ADD, AND register op
                end else begin
                    bypass_alu_1 <= 1'b0;
                    bypass_alu_2 <= 1'b0;
                end
                if (IR_Exec[15:12] === LD_op || IR_Exec[15:12] === LDR_op || IR_Exec[15:12] === LDI_op || IR_Exec[15:12] === LEA_op) begin
                    bypass_mem_1 <= IR[8:6] == IR_Exec[11:9];
                    bypass_mem_2 <= IR[2:0] == IR_Exec[11:9] && ~IR[5];  // only ADD, AND register op
                end else begin
                    bypass_mem_1 <= 1'b0;
                    bypass_mem_2 <= 1'b0;
                end
            end else if (IR[15:12] === ST_op || IR[15:12] === STI_op) begin
                if (IR_Exec[15:12] === ADD_op || IR_Exec[15:12] === AND_op || IR_Exec[15:12] === NOT_op) begin
                    bypass_alu_2 <= IR[11:9] == IR_Exec[11:9];
                end else begin
                    bypass_alu_2 <= 1'b0;
                end
                if (IR_Exec[15:12] === LD_op || IR_Exec[15:12] === LDR_op || IR_Exec[15:12] === LDI_op || IR_Exec[15:12] === LEA_op) begin
                    bypass_mem_2 <= IR[11:9] == IR_Exec[11:9] && ~IR[5];
                end else begin
                    bypass_mem_2 <= 1'b0;
                end
            end else if (IR[15:12] === STR_op) begin
                if (IR_Exec[15:12] === ADD_op || IR_Exec[15:12] === AND_op || IR_Exec[15:12] === NOT_op) begin
                    bypass_alu_1 <= IR[8:6]  == IR_Exec[11:9];
                    bypass_alu_2 <= IR[11:9] == IR_Exec;
                end else begin
                    bypass_alu_1 <= 1'b0;
                    bypass_alu_2 <= 1'b0;
                end
                if (IR_Exec[15:12] === LD_op || IR_Exec[15:12] === LDR_op || IR_Exec[15:12] === LDI_op || IR_Exec[15:12] === LEA_op) begin
                    bypass_mem_1 <= IR[8:6]  == IR_Exec[11:9];
                    bypass_mem_2 <= IR[11:9] == IR_Exec[11:9];
                end else begin
                    bypass_mem_1 <= 1'b0;
                    bypass_mem_2 <= 1'b0;
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
    always @ (*) begin
        if (rst) begin
            mem_state <= 2'h3;
        end
    end 
    
    always @ (*) begin
        if (IR_Exec[15:12] === LD_op || IR_Exec[15:12] === LDR_op) begin
            if (~complete_data) begin
                mem_state <= 2'h0;
            end 
        end else if (IR_Exec[15:12] === ST_op || IR_Exec[15:12] === STR_op) begin
            mem_state <= 2'h2;
        end else if (IR_Exec[15:12] === LDI_op || IR_Exec[15:12] === STI_op) begin
            if (~complete_data) begin
                mem_state <= 2'h1;
            end else begin
                if (IR_Exec[15:12] === LDI_op) begin
                    mem_state <= 2'h0;
                end else if (IR_Exec[15:12] === STI_op) begin
                    mem_state <= 2'h2;
                end
            end
        end else begin
            mem_state <= 2'h3;
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