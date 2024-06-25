`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit  { 
    instr_op,
    reset_op
} op_t;

///////////////////////////////////////////////

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
} instr_t;

///////////////////////////////////////////////

interface instr_mem_if;
    parameter INSTR_MEM_SIZE = 2**16;
    reg [15:0] instr_mem [0:INSTR_MEM_SIZE-1];
    
    initial begin
        instr_mem[16'h3000] = 16'h5020;  // AND // R0 <- R0 & 0 
        instr_mem[16'h3001] = 16'h2C20;  // LD  // R6 <- DMem[3024]
        instr_mem[16'h3002] = 16'h1422;  // ADD // R2 <- R0 + 2
        instr_mem[16'h3003] = 16'h12A1;  // ADD // R1 <- R2 + 1
        instr_mem[16'h3004] = 16'h5A81;  // AND // R5 <- R2 & R1
        instr_mem[16'h3005] = 16'hC180;  // JMP // JMP R6
        instr_mem[16'h3008] = 16'h967F;  // NOT // R3 <- ~R1
        instr_mem[16'h3009] = 16'h3600;  // ST  // R3 -> DMem[300A]
        instr_mem[16'h300A] = 16'h1AA5;  // ADD // R5 <- R2 + 5
        instr_mem[16'h300B] = 16'hA802;  // LDI // R4 <- DMem[3010]
        instr_mem[16'h300C] = 16'h5B01;  // AND // R5 <- R4 & R1
        instr_mem[16'h300D] = 16'h1421;  // ADD // R2 <- R0 + 1
        instr_mem[16'h300E] = 16'h0A04;  // BR  // R5 != 0
        instr_mem[16'h3014] = 16'h12A4;  // ADD // R1 <- R2 + 4
        instr_mem[16'h3015] = 16'h6F82;  // LDR // R7 <- DMem[300A]
        instr_mem[16'h3016] = 16'h1207;  // LEA // R5 <- 300C
        instr_mem[16'h3017] = 16'hEBF8;  // LEA // R5 <- 300C
        instr_mem[16'h3018] = 16'hB804;  // STI // R4 -> DMem[301B]
        instr_mem[16'h3019] = 16'h7545;  // STR // R2 -> DMem[3011]
    end
    
endinterface

///////////////////////////////////////////////

interface data_mem_if;
    parameter DATA_MEM_SIZE = 2**16;
    reg [15:0] data_mem [0:DATA_MEM_SIZE-1];
    
    initial begin
        data_mem[16'h300A] = 16'h300B;
        data_mem[16'h300F] = 16'h3011;
        data_mem[16'h3011] = 16'h0016;
        data_mem[16'h301e] = 16'h3020;
        data_mem[16'h3023] = 16'h3008;
    end
endinterface

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
    op_t         op;
    logic        complete_data;
    logic        complete_instr;
    logic [15:0] Instr_dout;
    logic [15:0] Data_dout;
    logic [15:0] PC;
    logic        instrmem_rd;
    logic [15:0] Data_addr;
    logic [15:0] Data_din;
    logic        Data_rd;        
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

class instr extends uvm_sequence#(transaction);
    `uvm_object_utils(instr)
    
    transaction tr;
    
    function new(string name = "instr");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = instr_op;
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class reset extends uvm_sequence#(transaction);
    `uvm_object_utils(reset)
    
    transaction tr;
    
    function new(string name = "reset");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = reset_op;
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual LC3_if       LC3_vif;
    virtual instr_mem_if instr_mem_vif;
    virtual data_mem_if  data_mem_vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!(uvm_config_db#(virtual LC3_if)::get(this,"","LC3_vif",LC3_vif) &&
             uvm_config_db#(virtual instr_mem_if)::get(this,"","instr_mem_vif",instr_mem_vif) &&
             uvm_config_db#(virtual data_mem_if)::get(this,"","data_mem_vif",data_mem_vif)))
            `uvm_error("MON", "Unable to access interfaces");
    endfunction
    
    task print_inputs();
        `uvm_info("DRV", $sformatf("rst: %01b, complete_data: %01b, complete_instr: %01b, Instr_dout: %04h, Data_dout: %04h",
                                    LC3_vif.rst,
                                    LC3_vif.complete_data,
                                    LC3_vif.complete_instr,
                                    LC3_vif.Instr_dout,
                                    LC3_vif.Data_dout), UVM_NONE);
    endtask
    
    task instr();
        @(posedge LC3_vif.clk);
        LC3_vif.complete_data  <= LC3_tb.dut.mem_state != 3;  // complete_data shoudl go low after read memory (mem_state = 0) or write memory (mem_state = 2)
        LC3_vif.complete_instr <= 1'b1;
        if (LC3_vif.instrmem_rd === 1'b1) begin
            if (LC3_vif.Instr_dout inside { BR_op, JMP_op }) begin
                LC3_vif.Instr_dout <= LC3_vif.Instr_dout;    
            end else begin
                LC3_vif.Instr_dout <= instr_mem_vif.instr_mem[LC3_vif.PC];
            end
        end else begin
            LC3_vif.Instr_dout <= LC3_vif.Instr_dout;
        end
        LC3_vif.Data_dout      <= data_mem_vif.data_mem[LC3_vif.Data_addr];
        `uvm_info("DRV", $sformatf("PC: %04h", LC3_vif.PC), UVM_NONE); 
        print_inputs();
    endtask
    
    task reset();
        LC3_vif.rst            <= 1'b1;
        LC3_vif.complete_data  <= 1'b0;
        LC3_vif.complete_instr <= 1'b0; 
        LC3_vif.Instr_dout     <= 16'h5020;  // AND R0, R0, #0 is the NOP instruction in this project
        LC3_vif.Data_dout      <= 16'b0;
        @(posedge LC3_vif.clk);
        print_inputs();
        repeat(4) @(posedge LC3_vif.clk); #7;
        LC3_vif.rst            <= 1'b0;
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            case(tr.op)
                instr_op: instr();
                reset_op: reset();
            endcase
            seq_item_port.item_done();
        end
    endtask
endclass

///////////////////////////////////////////////

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) send;
    
    virtual LC3_if LC3_vif;
    transaction tr;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual LC3_if)::get(this,"","LC3_vif",LC3_vif))
            `uvm_error("MON", "Unable to access interfaces");
    endfunction    
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge LC3_vif.clk); #0.001;
            if (LC3_vif.rst) begin
                tr.op = reset_op;
            end else begin
                tr.op = instr_op;
            end
            tr.Instr_dout  = LC3_vif.Instr_dout;
            tr.PC          = LC3_vif.PC; 
            tr.instrmem_rd = LC3_vif.instrmem_rd;
            tr.Data_addr   = LC3_vif.Data_addr;
            tr.Data_din    = LC3_vif.Data_din;
            tr.Data_rd     = LC3_vif.Data_rd;
            `uvm_info("MON", $sformatf("PC: %04h | instrmem_rd: %01b | Data_addr: %04h | Data_din: %04h | Data_rd: %01b",
                                        tr.PC,
                                        tr.instrmem_rd,
                                        tr.Data_addr,
                                        tr.Data_din,
                                        tr.Data_rd), UVM_NONE);
            send.write(tr);
        end
    endtask
endclass

///////////////////////////////////////////////

class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(scoreboard)
    
    uvm_analysis_imp#(transaction, scoreboard) recv;
    
    virtual instr_mem_if instr_mem_vif;
    virtual data_mem_if  data_mem_vif;
        
    int PC = 16'h3000;    
    logic [15:0] instr1 = 16'h5020, 
                 instr2 = 16'h5020, 
                 instr3 = 16'h5020, 
                 instr4 = 16'h5020, 
                 instr5 = 16'h5020;  // 5020: R0 <- R0 & 0 is NOP instr in this processor
    logic instrmem_rd_queue[$] = '{1'b1,1'b1};
    logic prev_instrmem_rd, instrmem_rd;
    bit [15:0] Data_addr_queue[$];                 
    
    function new(input string inst = "scoreboard", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
        if(!(uvm_config_db#(virtual instr_mem_if)::get(this,"","instr_mem_vif",instr_mem_vif) &&
             uvm_config_db#(virtual data_mem_if)::get(this,"","data_mem_vif",data_mem_vif)))
            `uvm_error("MON", "Unable to access interfaces");
    endfunction    
    
    function void verify_PC(transaction tr, logic [15:0] instr1, instr2, instr3, instr4, instr5);
        if (tr.op == reset_op) begin
            if (tr.PC == 16'h3000) begin
                `uvm_info("SCO", "PC MATCH", UVM_NONE);                
            end else begin
                `uvm_error("SCO", "PC MISMATCH");
            end
        end else if (tr.op == instr_op) begin
            if (instr1[15:12] === BR_op && instr2[15:12] === BR_op && instr3[15:12] === BR_op && instr4[15:12] === BR_op) begin
                PC = PC + 1 + { {7{tr.Instr_dout[8]}}, tr.Instr_dout[8:0] };  // BR is taken
            end else if (instr1[15:12] === JMP_op && instr2[15:12] === JMP_op && instr3[15:12] === JMP_op && instr4[15:12] === JMP_op) begin
                PC = LC3_tb.dut.w.rf.register_files[tr.Instr_dout[8:6]];      // JMP is taken
            end else if (instr4[15:12] inside { LD_op, LDR_op, ST_op, STR_op } || instr5[15:12] inside { LDI_op, STI_op }) begin
                PC = PC;
            end else if (instr1[15:12] inside { BR_op, JMP_op } && instr2[15:12] inside { BR_op, JMP_op }) begin
                PC = PC;  // allow bubbles to pass
            end else begin
                PC = PC + 1;
            end           
            if (instr2 !== 16'hxxxx) begin
                if (tr.PC != PC) begin
                    `uvm_error("SCO", $sformatf("PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                end else begin
                    `uvm_info("SCO", "PC MATCH", UVM_NONE);
                end
            end
        end
    endfunction 
    
    function void verify_instrmem_rd(transaction tr, logic [15:0] instr1, instr2, instr3, instr4, instr5);
        if (tr.op == reset_op) begin
            if (tr.instrmem_rd === 1'bz) begin
                `uvm_info("SCO", "instrmem_rd MATCH", UVM_NONE);
            end else begin
                `uvm_error("SCO", "instrmem_rd MISMATCH");
            end
        end else if (tr.op == instr_op) begin
            if (tr.Instr_dout[15:12] inside { ADD_op, AND_op, NOT_op, LEA_op } && instrmem_rd_queue[0] === 1'b1) begin
                instrmem_rd_queue.push_back(1'b1);
            end else if (tr.Instr_dout[15:12] inside { LD_op, LDR_op, ST_op, STR_op } && instrmem_rd_queue[0] === 1'b1) begin
                instrmem_rd_queue.push_back(1'bz);
                instrmem_rd_queue.push_back(1'b1);
            end else if (tr.Instr_dout[15:12] inside { LDI_op, STI_op } && instrmem_rd_queue[0] === 1'b1) begin
                instrmem_rd_queue.push_back(1'bz);
                instrmem_rd_queue.push_back(1'bz);
                instrmem_rd_queue.push_back(1'b1);
            end else if (tr.Instr_dout[15:12] inside { BR_op, JMP_op } && instrmem_rd === 1'b1) begin
                instrmem_rd_queue = '{1'bz, 1'bz, 1'bz, 1'b1, 1'b1, 1'b1};
            end
            instrmem_rd = instrmem_rd_queue.pop_front();
            if (instr3 !== 16'hxxxx) begin
                if (tr.instrmem_rd === instrmem_rd) begin
                    `uvm_info("SCO", "instrmem_rd MATCH", UVM_NONE);
                end else begin
                    `uvm_error("SCO", "instrmem_rd MISMATCH");
                end
            end                
            prev_instrmem_rd = instrmem_rd;            
        end
    endfunction
    
    function void verify_Data_addr(transaction tr);
        if (tr.op == reset_op) begin
            if (tr.Data_addr === 16'bzzzz) begin
                `uvm_info("SCO", "Data_addr MATCH", UVM_NONE);
            end else begin
                `uvm_error("SCO", "Data_addr MISMATCH");
            end
        end else if (tr.op == instr_op) begin
            case(tr.Instr_dout[15:12])
                (LD_op  || ST_op):  Data_addr_queue.push_back(calc_LD_ST_Data_addr(tr));
                (LDR_op || STR_op): Data_addr_queue.push_back(calc_LDR_STR_Data_addr(tr));
                (LDI_op || STI_op): Data_addr_queue.push_back(calc_LDI_STI_Data_addr(tr));
                BR_op:              Data_addr_queue.push_back(calc_BR_Data_addr(tr));
                JMP_op:             Data_addr_queue.push_back(calc_JMP_Data_addr(tr));
            endcase
            if (instrmem_rd === 1'bz) begin
                if (tr.Data_addr === Data_addr_queue.pop_front()) begin
                    `uvm_info("SCO", "Data_addr MATCH", UVM_NONE);
                end else begin
                    `uvm_error("SCO", "Data_addr MISMATCH");
                end
            end
        end
    endfunction
    
    function bit [15:0] calc_LD_ST_Data_addr(transaction tr);
        return PC + { {7{tr.Instr_dout[8]}}, tr.Instr_dout[8:0] };
    endfunction
    
    function bit [15:0] calc_LDR_STR_Data_addr(transaction tr);
        return LC3_tb.dut.w.rf.register_files[tr.Instr_dout[8:6]] + { {10{tr.Instr_dout[5]}}, tr.Instr_dout[5:0] };
    endfunction
    
    function bit [15:0] calc_LDI_STI_Data_addr(transaction tr);
        return data_mem_vif.data_mem[PC + { {7{tr.Instr_dout[8]}}, tr.Instr_dout[8:0] }];
    endfunction
    
    function bit [15:0] calc_BR_Data_addr(transaction tr);
        
    endfunction
    
    function bit [15:0] calc_JMP_Data_addr(transaction tr);
        return LC3_tb.dut.w.rf.register_files[tr.Instr_dout[8:6]];
    endfunction
    
    virtual function void write(transaction tr);
        instr5 = instr4;
        instr4 = instr3;
        instr3 = instr2;
        instr2 = instr1;
        instr1 = tr.Instr_dout;
        verify_PC(tr, instr1, instr2, instr3, instr4, instr5);
        verify_instrmem_rd(tr, instr1, instr2, instr3, instr4, instr5);
        verify_Data_addr(tr);
        $display("---------------------------------------------");
    endfunction    
endclass

///////////////////////////////////////////////

class agent extends uvm_agent;
    `uvm_component_utils(agent)
    
    function new(input string inst = "agent", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    driver d;
    uvm_sequencer#(transaction) seqr;
    monitor m;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m = monitor::type_id::create("m", this);
        d = driver::type_id::create("d", this);
        seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

///////////////////////////////////////////////

class environment extends uvm_env;
    `uvm_component_utils(environment)
    
    function new(input string inst = "environment", uvm_component c);
        super.new(inst, c);
    endfunction
    
    agent a;
    scoreboard s;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = agent::type_id::create("a", this);
        s = scoreboard::type_id::create("s", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);
    endfunction
endclass

///////////////////////////////////////////////

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(input string inst = "test", uvm_component c);
        super.new(inst, c);
    endfunction
    
    environment e;
    instr i;
    reset r;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = environment::type_id::create("environment", this);
        i = instr::type_id::create("i");
        r = reset::type_id::create("r");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        r.start(e.a.seqr);
        for (int n = 0; n < 37; n++) begin
            i.start(e.a.seqr);
        end
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module LC3_tb;
    LC3_if       LC3_vif();
    instr_mem_if instr_mem_vif();
    data_mem_if  data_mem_vif();
    
    LC3 dut(
        .clk(LC3_vif.clk),
        .rst(LC3_vif.rst),
        .complete_data(LC3_vif.complete_data),
        .complete_instr(LC3_vif.complete_instr),
        .Instr_dout(LC3_vif.Instr_dout),
        .Data_dout(LC3_vif.Data_dout),
        .PC(LC3_vif.PC),
        .instrmem_rd(LC3_vif.instrmem_rd),
        .Data_addr(LC3_vif.Data_addr),
        .Data_din(LC3_vif.Data_din),
        .Data_rd(LC3_vif.Data_rd)
    );
    
    initial begin
        LC3_vif.clk <= 0;        
    end
    
    always #5 LC3_vif.clk <= ~LC3_vif.clk;
    
    initial begin
        uvm_config_db#(virtual LC3_if)::set(null, "*", "LC3_vif", LC3_vif);
        uvm_config_db#(virtual instr_mem_if)::set(null, "*", "instr_mem_vif", instr_mem_vif);
        uvm_config_db#(virtual data_mem_if)::set(null, "*", "data_mem_vif", data_mem_vif);
        run_test("test");
    end   
endmodule