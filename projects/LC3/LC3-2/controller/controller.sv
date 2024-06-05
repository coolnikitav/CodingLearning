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
    
    op_t alu_ops [2:0] = {ADD_op, AND_op, NOT_op); 
               
    typedef enum bit [2:0] { 
        IDLE      = 3'h0,
        UPDATE_PC = 3'h1,
        FETCH     = 3'h2,
        DECODE    = 3'h3,
        EXECUTE   = 3'h4,
        MEMACCESS = 3'h5,
        WRITEBACK = 3'h6
    } state_t;
    
    state_t current_state, next_state;
    
    typedef enum bit [1:0] {
        READ_MEM       = 2'h0,
        READ_MEM_INDIR = 2'h1,
        WRITE_MEM      = 2'h2,
        INIT_STATE     = 2'h3
    } mem_state_t;
    
    mem_state_t current_mem_state, next_mem_state;
    
    /*
     *  State transition logic
     */
    always @ (*) begin
        case (current_state)
            IDLE:      next_state = FETCH;
            FETCH:     next_state = complete_instr ? DECODE : FETCH;
            DECODE:    next_state = EXECUTE;   
            EXECUTE: begin
                if (IR[15:12] inside mem_ops) begin
                    next_state = MEMACCESS;
                end else begin
                    next_state = WRITEBACK;
                end
            end
            MEMACCESS: begin
                
            end
            WRITEBACK: next_state = FETCH;
            default:   next_state = IDLE; 
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
                bypass_alu_1     <= 1'b0;
                bypass_alu_2     <= 1'b0;
                bypass_mem_1     <= 1'b0;
                bypass_mem_2     <= 1'b0;
                mem_state        <= 2'h3; // MEM_IDLE
                br_taken         <= 1'b0;
            end
            FETCH: begin
                if (complete_instr) begin
                    enable_fetch    <= 1'b1;
                    enable_updatePC <= 1'b1;
                end
            end
            DECODE: begin
                enable_decode <= 1'b1;
            end
            EXECUTE: begin
                enable_execute <= 1'b1;
            end
            MEMACCESS: begin
                enable_execute <= 1'b0;
                if (IMem_dout[15:12] == 4'b0110 || IMem_dout[15:12] == 4'b0111) begin          // Check for LD, LDR, LDI
                    mem_state <= 2'b00; // MEM_READ
                end else if (IMem_dout[15:12] == 4'b0011 || IMem_dout[15:12] == 4'b1011) begin // Check for ST, STR, STI
                    mem_state <= 2'b10; // MEM_WRITE
                end
            end
            WRITEBACK: begin
                enable_writeback <= 1'b1;
                mem_state <= 2'b11; // MEM_IDLE
            end
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
            if ((IR_Exec[11:9] == IR[8:6]) && (IR_Exec[11:9] != 3'b000)) begin
                bypass_alu_1 <= 1'b1;
            end else begin
                bypass_alu_1 <= 1'b0;
            end
            if ((IR_Exec[11:9] == IR[2:0]) && (IR_Exec[11:9] != 3'b000)) begin
                bypass_alu_2 <= 1'b1;
            end else begin
                bypass_alu_2 <= 1'b0;
            end
        end else if (IR_Exec[15:12] == 4'b0101) begin // AND instruction
            if ((IR_Exec[11:9] == IR[8:6]) && (IR_Exec[11:9] != 3'b000)) begin
                bypass_alu_1 <= 1'b1;
            end else begin
                bypass_alu_1 <= 1'b0;
            end
            if ((IR_Exec[11:9] == IR[2:0]) && (IR_Exec[11:9] != 3'b000)) begin
                bypass_alu_2 <= 1'b1;
            end else begin
                bypass_alu_2 <= 1'b0;
            end
        end else begin
            bypass_alu_1 <= 1'b0;
            bypass_alu_2 <= 1'b0;
        end

        if (IR_Exec[15:12] == 4'b0110) begin // LD instruction
            if ((IR_Exec[11:9] == IR[8:6]) && (IR_Exec[11:9] != 3'b000)) begin
                bypass_mem_1 <= 1'b1;
            end else begin
                bypass_mem_1 <= 1'b0;
            end
        end else begin
            bypass_mem_1 <= 1'b0;
        end

        if (IR_Exec[15:12] == 4'b1001) begin // NOT instruction
            if ((IR_Exec[11:9] == IR[8:6]) && (IR_Exec[11:9] != 3'b000)) begin
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
