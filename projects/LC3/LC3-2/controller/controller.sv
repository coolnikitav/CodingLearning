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
    output [2:0]  mem_state
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
               
    typedef enum bit [3:0] { 
        IDLE            = 3'd0,
        UPDATE_PC       = 3'd1,
        FETCH           = 3'd2,
        DECODE          = 3'd3,
        EXECUTE_ALU     = 3'd4,
        EXECUTE_CONTROL = 3'd5,
        EXECUTE_MEM     = 3'd6,
        READ_MEM_INDIR  = 3'd7,
        READ_MEM        = 3'd8,
        WRITE_MEM       = 3'd9,
        WRITEBACK       = 3'd10
    } state_t;
    
    state_t current_state, next_state;
    
    /*
     *  State transition logic
     */
    always @ (*) begin
        case (current_state)
            IDLE:      next_state = FETCH;
            UPDATE_PC: next_state = FETCH;
            FETCH:     next_state = complete_instr ? DECODE : FETCH;
            DECODE: begin
                if (IR[15:12] inside { ADD_op, AND_op, NOT_op }) begin
                    next_state = EXECUTE_ALU;
                end else if (IR[15:12] inside { BR_op, JMP_op }) begin
                    next_state = EXECUTE_CONTROL;
                end else if (IR[15:12] inside { LD_op, LDR_op, LDI_op, LEA_op, ST_op, STR_op, STI_op }) begin 
                    next_state = EXECUTE_MEM;
                end
            end
            EXECUTE_ALU:     next_state = WRITEBACK;
            EXECUTE_CONTROL: next_state = WRITEBACK;
            EXECUTE_MEM: begin
                if (IR_Exec[15:12] inside { LDI_op, STI_op }) begin
                    next_state = READ_MEM_INDIR; 
                end else if (IR_Exec[15:12] inside { ST_op, STR_op }) begin
                    next_state = WRITE_MEM;
                end else if (IR_Exec[15:12] inside { LD_op, LDR_op }) begin
                    next_state = READ_MEM;
                end else if (IR_Exec[15:12] == LEA_op) begin
                    next_state = WRITEBACK;
                end
            end
            READ_MEM_INDIR: begin
                if (IR_Exec[15:12] == LDI_op) begin
                    next_state = complete_data ? READ_MEM : READ_MEM_INDIR;
                end else if (IR_Exec[15:12] == STI_op) begin
                    next_state = complete_data ? WRITE_MEM : READ_MEM_INDIR;
                end
            end
            READ_MEM:  next_state = complete_data ? WRITEBACK : READ_MEM;
            WRITE_MEM: next_state = complete_data ? UPDATE_PC : WRITE_MEM;
            WRITEBACK: next_state = UPDATE_PC;
        endcase
    end
    
    /*
     *  State flip-flops with synchronous reset
     */
    always @ (posedge clk) begin
        if (rst) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end
    
    assign mem_state = current_state == REAM_MEM_INDIR ? 2'h1 : 
                                        READ_MEM       ? 2'h0 :
                                        WRITE_MEM      ? 2'h2 :
                                                         2'h3;
    /*
     *  Output logic
     */
    always @(posedge clk) begin
        case (current_state)
            IDLE: begin
                enable_updatePC  <= 1'b0;
                enable_fetch     <= 1'b0;
                enable_decode    <= 1'b0;
                enable_execute   <= 1'b0;
                enable_writeback <= 1'b0;
            end
            UPDATE_PC:
            FETCH:
            DECODE:
            EXECUTE_ALU:
            EXECUTE_CONTROL = 3'd5,
            EXECUTE_MEM     = 3'd6,
            READ_MEM_INDIR  = 3'd7,
            READ_MEM        = 3'd8,
            WRITE_MEM       = 3'd9,
            WRITEBACK       = 3'd10
            endcase

        // Control signal for branch
        if (IR[15:12] == 4'b0000) begin // BR instruction
            if ((IR[11:9] & psr) != 3'b000) begin
                br_taken <= 1'b1;
            end else begin
                br_taken <= 1'b0;
            end
        end else if (IR[15:12] == 4'b1100) begin // JMP instruction
            br_taken <= 1'b1;
        end else begin
            br_taken <= 1'b0;
        end

        // Bypass logic
        if (IR_Exec[15:12] == 4'b0001) begin // ADD instruction
            if (IR_Exec[11:9] == IR[8:6]) begin
                bypass_alu_1 <= 1'b1;
            end else begin
                bypass_alu_1 <= 1'b0;
            end
            if (IR_Exec[11:9] == IR[2:0]) begin
                bypass_alu_2 <= 1'b1;
            end else begin
                bypass_alu_2 <= 1'b0;
            end
        end else if (IR_Exec[15:12] == 4'b0101) begin // AND instruction
            if (IR_Exec[11:9] == IR[8:6]) begin
                bypass_alu_1 <= 1'b1;
            end else begin
                bypass_alu_1 <= 1'b0;
            end
            if (IR_Exec[11:9] == IR[2:0]) begin
                bypass_alu_2 <= 1'b1;
            end else begin
                bypass_alu_2 <= 1'b0;
            end
        end else begin
            bypass_alu_1 <= 1'b0;
            bypass_alu_2 <= 1'b0;
        end

        if (IR_Exec[15:12] == 4'b0110) begin // LD instruction
            if (IR_Exec[11:9] == IR[8:6]) begin
                bypass_mem_1 <= 1'b1;
            end else begin
                bypass_mem_1 <= 1'b0;
            end
        end else begin
            bypass_mem_1 <= 1'b0;
        end

        if (IR_Exec[15:12] == 4'b1001) begin // NOT instruction
            if (IR_Exec[11:9] == IR[8:6]) begin
                bypass_mem_2 <= 1'b1;
            end else begin
                bypass_mem_2 <= 1'b0;
            end
        end else begin
            bypass_mem_2 <= 1'b0;
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
