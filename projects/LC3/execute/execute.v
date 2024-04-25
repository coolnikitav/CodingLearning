module execute(
    input             clk,
    input             rst,
    input             enable_execute,
    input      [5:0]  E_control,
    input      [15:0] IR,
    input      [15:0] npc_in,
    input      [1:0]  W_control_in,
    output     [15:0] aluout,
    output reg [1:0]  W_control_out,
    input      [15:0] VSR1,
    input      [15:0] VSR2,
    output reg [2:0]  dr,
    output     [2:0]  sr1,
    output     [2:0]  sr2,
    output reg [15:0] pcout
    );
    
    /*
     *  E_control bus
     */
    wire [1:0] alu_control, pcselect1;
    wire       pcselect2,   op2select;
    assign alu_control = E_control[5:4];
    assign pcselect1   = E_control[3:2];
    assign pcselect2   = E_control[1];
    assign op2select   = E_control[0];
    
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
    
    always @ (*) begin
        pcout = pcout1 + pcout2;
    end
    
    /*
     *  ALU calculation
     */
    reg [15:0] aluin2;  // aluin1 is always VSR1, aluin2 could be VSR2 or an imm
    
    always @ (*) begin
        case (op2select)
            1'h0: aluin2 = imm5;
            1'h1: aluin2 = VSR2;
        endcase
    end
    
    alu a (
        .clk(clk),
        .rst(rst),
        .enable(enable_execute),
        .alu_control(alu_control),
        .aluin1(VSR1),
        .aluin2(aluin2),
        .aluout(aluout)
    );
    
    /*
     *  Output control
     */ 
    always @ (posedge clk) begin
        if (rst == 1'b1) begin
            W_control_out <= 16'h0;
            dr            <= 3'h0;
            pcout         <= 16'h0;
        end else if (enable_execute == 1'b1) begin
            W_control_out <= W_control_in;
            dr            <= IR[11:9];            
        end
    end
    
    assign sr1 = IR[8:6];
    assign sr2 = IR[2:0];
endmodule
