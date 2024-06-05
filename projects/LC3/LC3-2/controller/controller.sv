module Controller (
    input wire clock,
    input wire reset,
    input wire complete_data,
    input wire complete_instr,
    input wire [15:0] IR,
    input wire [15:0] IR_Exec,
    input wire [2:0] NZP,
    input wire [2:0] psr,
    output reg enable_updatePC,
    output reg enable_fetch,
    output reg enable_decode,
    output reg enable_execute,
    output reg enable_writeback,
    output reg bypass_alu_1,
    output reg bypass_alu_2,
    output reg bypass_mem_1,
    output reg bypass_mem_2,
    output reg [1:0] mem_state,
    output reg br_taken
);

// State definitions
typedef enum reg [2:0] {
    IDLE = 3'b000,
    FETCH = 3'b001,
    DECODE = 3'b010,
    EXECUTE = 3'b011,
    MEM_ACCESS = 3'b100,
    WRITEBACK = 3'b101
} state_t;

// State variables
state_t current_state, next_state;

// Initial state
initial begin
    current_state = IDLE;
end

// Control signal generation
always @(posedge clock or posedge reset) begin
    if (reset) begin
        current_state <= IDLE;
        enable_updatePC <= 1'b0;
        enable_fetch <= 1'b0;
        enable_decode <= 1'b0;
        enable_execute <= 1'b0;
        enable_writeback <= 1'b0;
        bypass_alu_1 <= 1'b0;
        bypass_alu_2 <= 1'b0;
        bypass_mem_1 <= 1'b0;
        bypass_mem_2 <= 1'b0;
        mem_state <= 2'b11; // MEM_IDLE
        br_taken <= 1'b0;
    end else begin
        current_state <= next_state;

        case (current_state)
            IDLE: begin
                enable_updatePC <= 1'b0;
                enable_fetch <= 1'b0;
                enable_decode <= 1'b0;
                enable_execute <= 1'b0;
                enable_writeback <= 1'b0;
                bypass_alu_1 <= 1'b0;
                bypass_alu_2 <= 1'b0;
                bypass_mem_1 <= 1'b0;
                bypass_mem_2 <= 1'b0;
                mem_state <= 2'b11; // MEM_IDLE
                br_taken <= 1'b0;
                next_state <= FETCH;
            end
            FETCH: begin
                enable_fetch <= 1'b1;
                if (complete_instr) begin
                    enable_fetch <= 1'b0;
                    enable_updatePC <= 1'b1;
                    next_state <= DECODE;
                end else begin
                    next_state <= FETCH;
                end
            end
            DECODE: begin
                enable_decode <= 1'b1;
                next_state <= EXECUTE;
            end
            EXECUTE: begin
                enable_execute <= 1'b1;
                enable_decode <= 1'b0;
                next_state <= MEM_ACCESS;
            end
            MEM_ACCESS: begin
                enable_execute <= 1'b0;
                if (IR_Exec[15:12] == 4'b0110 || IR_Exec[15:12] == 4'b0111) begin // Check for LD, LDR, LDI
                    mem_state <= 2'b00; // MEM_READ
                    if (complete_data) begin
                        next_state <= WRITEBACK;
                    end else begin
                        next_state <= MEM_ACCESS;
                    end
                end else if (IR_Exec[15:12] == 4'b0011 || IR_Exec[15:12] == 4'b1011) begin // Check for ST, STR, STI
                    mem_state <= 2'b10; // MEM_WRITE
                    if (complete_data) begin
                        next_state <= FETCH;
                    end else begin
                        next_state <= MEM_ACCESS;
                    end
                end else begin
                    next_state <= WRITEBACK;
                end
            end
            WRITEBACK: begin
                enable_writeback <= 1'b1;
                mem_state <= 2'b11; // MEM_IDLE
                next_state <= FETCH;
            end
            default: begin
                next_state <= IDLE;
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
end

endmodule

