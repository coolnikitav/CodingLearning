module execute(
    input             clk,
    input             rst,
    input             enable_execute,
    input      [5:0]  E_Control_in,
    input      [1:0]  W_Control_in,
    input             Mem_Control_in,
    input             bypass_alu_1,
    input             bypass_alu_2,
    input             bypass_mem_1,
    input             bypass_mem_2,
    input      [15:0] IR,
    input      [15:0] npc_in,
    input      [15:0] Mem_Bypass_val,
    output reg [15:0] aluout,
    output reg [1:0]  W_Control_out,
    output reg        Mem_Control_out,
    output reg [15:0] M_Data,
    input      [15:0] VSR1,
    input      [15:0] VSR2,
    output reg [2:0]  dr,
    output reg [2:0]  sr1,
    output reg [2:0]  sr2,
    output reg [15:0] pcout,
    output reg [2:0]  NZP,
    output reg [15:0] IR_Exec
    );
    /*
     *  E_control bus
     */
    wire [1:0] alu_control, pcselect1;
    wire       pcselect2,   op2select;
    assign alu_control = E_Control_in[5:4];
    assign pcselect1   = E_Control_in[3:2];
    assign pcselect2   = E_Control_in[1];
    assign op2select   = E_Control_in[0];
    
    /*
     *  extension calculation
     */
    wire [15:0] imm5, offset6, offset9, offset11;
    extension e (
        .IR(IR),
        .imm5(imm5),
        .offset6(offset6),
        .offset9(offset9),
        .offset11(offset11)
    );
    
    /*
     *  pcout calculation
     */
    reg [15:0] pcout1, pcout2;
        
    always @ (*) begin
        case (pcselect1)
            2'h0: pcout1 = offset11;
            2'h1: pcout1 = offset9;
            2'h2: pcout1 = offset6;
            2'h3: pcout1 = imm5;
        endcase
    end
    
    always @ (*) begin
        case (pcselect2)
            2'h0: pcout2 = VSR1;
            2'h1: pcout2 = npc_in;
        endcase
    end
    
    always @ (posedge clk) begin
        if (rst) begin
            pcout <= 16'h0;
        end else begin
            pcout <= pcout1 + pcout2;
        end
    end
    
    /*
     *  ALU calculation
     */
    reg [15:0] src1_val, src2_val; 
    
    always @ (*) begin
        if (bypass_alu_1) begin
            src1_val = aluout;
        end else if (bypass_mem_1) begin
            src1_val = Mem_Bypass_val;
        end else begin
            src1_val = VSR1;
        end
    end
    
    always @ (*) begin
        if (bypass_alu_2) begin
            src2_val = aluout;
        end else if (bypass_mem_2) begin
            src2_val = Mem_Bypass_val;
        end else begin
            case (op2select)
                1'h0: src2_val = imm5;
                1'h1: src2_val = VSR2;
            endcase
        end
    end
    
    alu a (
        .clk(clk),
        .rst(rst),
        .enable(enable_execute),
        .alu_control(alu_control),
        .aluin1(src1_val),
        .aluin2(src2_val),
        .aluout(aluout)
    );
    
    /*
     *  Output control
     */ 
    always @ (posedge clk) begin
        if (rst) begin
            W_Control_out   <= 2'h0;
            Mem_Control_out <= 1'h0;
            M_Data          <= 16'h0;
            dr              <= 3'h0; 
            NZP             <= 3'h0; 
            IR_Exec         <= 16'h0;         
        end else if (enable_execute == 1'b1) begin
            W_Control_out   <= W_Control_in;
            Mem_Control_out <= Mem_Control_in;
            if (IR[15:12] == 4'b0011 || IR[15:12] == 4'b0011 || IR[15:12] == 4'b0011) begin  // ST,STR,STI
                M_Data      <= src1_val;
            end else begin
                M_Data      <= 0;
            end
            if (IR[15:12] == 4'b0000) begin  // BR
                NZP         <= IR[11:9];
            end else begin
                NZP         <= 3'h0; 
            end
            dr              <= IR[11:9]; 
            IR_Exec         <= IR;           
        end else begin
            NZP             <= 3'h0;  // when enable_execute is low, NZP goes to 000 synchronously
        end
    end
    
    assign sr1 = IR[8:6];
    assign sr2 = IR[2:0];
endmodule

///////////////////////////////////////////////

interface execute_if;
    logic        clk;
    logic        rst;
    logic        enable_execute;
    logic [5:0]  E_Control_in;
    logic [1:0]  W_Control_in;
    logic        Mem_Control_in;
    logic        bypass_alu_1;
    logic        bypass_alu_2;
    logic        bypass_mem_1;
    logic        bypass_mem_2;
    logic [15:0] IR;
    logic [15:0] npc_in;
    logic [15:0] Mem_Bypass_val;
    logic [15:0] aluout;
    logic [1:0]  W_Control_out;
    logic        Mem_Control_out;
    logic [15:0] M_Data;
    logic [15:0] VSR1;
    logic [15:0] VSR2;
    logic [2:0]  dr;
    logic [2:0]  sr1;
    logic [2:0]  sr2;
    logic [15:0] pcout;
    logic [2:0]  NZP;
    logic [15:0] IR_Exec;
endinterface