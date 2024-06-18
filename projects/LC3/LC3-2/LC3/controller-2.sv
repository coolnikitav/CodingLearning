module Controller (
    input wire clock,
    input wire reset,
    input wire complete_instr,
    input wire complete_data,
    input wire [15:0] IR,            // Current instruction from decode stage
    input wire [2:0] psr,            // Processor status register (NZP flags)
    input wire [2:0] NZP,            // Condition codes from the Execute stage
    output reg enable_updatePC,
    output reg enable_fetch,
    output reg enable_decode,
    output reg enable_execute,
    output reg enable_writeback,
    output reg br_taken,
    output reg [1:0] mem_state       // State signal for memory operations
);

    // Extract the opcode from the instruction
    wire [3:0] opcode = IR[15:12];

    // Extract the condition codes for branch instructions
    wire [2:0] branch_condition = IR[11:9];

    // Intermediate signals for condition evaluation
    wire branch_condition_met;
    wire is_branch_instruction;
    wire is_jump_instruction;
    wire stall;

    // Determine if the branch condition is met
    assign branch_condition_met = |(psr & branch_condition);
    assign is_branch_instruction = (opcode == 4'b0000); // BR instruction
    assign is_jump_instruction = (opcode == 4'b1100); // JMP instruction

    // Example stall signal for simplicity; in practice, this could depend on many factors
    assign stall = (complete_instr == 0) || (complete_data == 0);

    always @(*) begin
        if (reset) begin
            br_taken = 0;
            enable_fetch = 0;
            enable_updatePC = 0;
            enable_decode = 0;
            enable_execute = 0;
            enable_writeback = 0;
            mem_state = 2'b00;
        end else begin
            // Default values
            br_taken = 0;
            enable_fetch = 1;
            enable_updatePC = 1;
            enable_decode = 1;
            enable_execute = 1;
            enable_writeback = 1;
            mem_state = 2'b00;

            if (is_branch_instruction) begin
                br_taken = branch_condition_met;
                if (!branch_condition_met) begin
                    enable_updatePC = 1; // Continue to next instruction
                end else begin
                    enable_updatePC = 1; // Take branch
                end
            end else if (is_jump_instruction) begin
                br_taken = 1; // Unconditional jump
                enable_updatePC = 1; // Update PC to target address
            end else begin
                br_taken = 0;
                enable_updatePC = 1;
            end

            // Handle stalls
            if (stall) begin
                enable_fetch = 0;
                enable_updatePC = 0;
                enable_decode = 0;
                enable_execute = 0;
                enable_writeback = 0;
            end
        end
    end

endmodule
