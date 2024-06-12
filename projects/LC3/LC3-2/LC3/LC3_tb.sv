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
        instr_mem[16'h3003] = 16'h1280;  // ADD // R1 <- R2 + 0)
        instr_mem[16'h3004] = 16'hC180;  // JMP // JMP R6
        instr_mem[16'h3008] = 16'h967F;  // NOT // R3 <- ~R1
        instr_mem[16'h3009] = 16'h3600;  // ST  // R3 -> DMem[300A]
        instr_mem[16'h300A] = 16'h1A83;  // ADD // R5 <- R2 + R3
        instr_mem[16'h300B] = 16'hA802;  // LDI // R4 <- DMem[3010]
        instr_mem[16'h300C] = 16'h5B01;  // AND // R5 <- R4 & R1
        instr_mem[16'h300D] = 16'h0A04;  // BR  // R5 != 0
        instr_mem[16'h3012] = 16'h52A4;  // ADD // R1 <- R2 + 4
        instr_mem[16'h3013] = 16'h6F82;  // LDR // R7 <- DMem[300A]
        instr_mem[16'h3014] = 16'hEBF8;  // LEA // R5 <- 300C
        instr_mem[16'h3015] = 16'hB804;  // STI // R4 -> DMem[301B]
        instr_mem[16'h3016] = 16'h7545;  // STR // R2 -> DMem[3011]
    end
    
endinterface

///////////////////////////////////////////////

interface data_mem_if;
    parameter DATA_MEM_SIZE = 2**16;
    reg [15:0] data_mem [0:DATA_MEM_SIZE-1];
    
    initial begin
        data_mem[16'h300A] = 16'h300B;
        data_mem[16'h300E] = 16'h3010;
        data_mem[16'h3010] = 16'h0015;
        data_mem[16'h301A] = 16'h301B;
        data_mem[16'h3024] = 16'h3008;
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
    logic        Data_addr;
    logic        Data_din;
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
        LC3_vif.rst            <= 1'b0;
        LC3_vif.complete_data  <= LC3_vif.Data_rd;
        LC3_vif.complete_instr <= 1'b1; //LC3_vif.instrmem_rd;
        LC3_vif.Instr_dout     <= instr_mem_vif.instr_mem[LC3_vif.PC];
        `uvm_info("DRV", $sformatf("PC: %04h", LC3_vif.PC), UVM_NONE); 
        LC3_vif.Data_dout      <= LC3_vif.Data_rd ? data_mem_vif.data_mem[LC3_vif.Data_addr] : 16'h0;
        @(posedge LC3_vif.clk);
        print_inputs(); #0.002;
    endtask
    
    task reset();
        LC3_vif.rst            <= 1'b1;
        LC3_vif.complete_data  <= 1'b0;
        LC3_vif.complete_instr <= 1'b0; 
        LC3_vif.Instr_dout     <= 16'b0;
        LC3_vif.Data_dout      <= 16'b0;
        @(posedge LC3_vif.clk);
        print_inputs();
        repeat(4) @(posedge LC3_vif.clk); #0.002;
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
    
    virtual LC3_if       LC3_vif;
    virtual instr_mem_if instr_mem_vif;
    virtual data_mem_if  data_mem_vif;
        
    int PC = 16'h3000;
    int stalled_cycles = 0;
    
    function new(input string inst = "scoreboard", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
        if(!(uvm_config_db#(virtual LC3_if)::get(this,"","LC3_vif",LC3_vif) &&
             uvm_config_db#(virtual instr_mem_if)::get(this,"","instr_mem_vif",instr_mem_vif) &&
             uvm_config_db#(virtual data_mem_if)::get(this,"","data_mem_vif",data_mem_vif)))
            `uvm_error("MON", "Unable to access interfaces");
    endfunction        
    
    virtual function void write(transaction tr);
        /* PC compare logic
        
           If instr = ADD, AND, NOT,     then PC++
           If instr = JMP, BR, LDI, STI, then PC stays the same for 2 additional cycles
           If instr = LD, ST, LDR, STR,  then PC stays the same for 1 additional cycle
        */
        if (tr.op == reset_op) begin
            if (tr.PC != 16'h3000) begin
                `uvm_error("SCO", "1 PC MISMATCH");
            end else begin
                `uvm_info("SCO", "PC MATCH", UVM_NONE);
            end
        end else if (tr.op == instr_op) begin
            if (instr_mem_vif.instr_mem[PC][15:12] inside { AND_op, ADD_op, NOT_op }) begin
                if (tr.PC != PC) begin
                    `uvm_error("SCO", $sformatf("2 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                end else begin
                    `uvm_info("SCO", "PC MATCH", UVM_NONE);
                end   
                PC = PC + 1;         
            end else if (instr_mem_vif.instr_mem[PC][15:12] inside { LDI_op, STI_op }) begin
                if (stalled_cycles == 0) begin
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("3 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                    PC = PC + 1;
                    stalled_cycles = 2;
                end else begin
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("4 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                    stalled_cycles = stalled_cycles-1;
                end
            end else if (instr_mem_vif.instr_mem[PC][15:12] inside { BR_op, JMP_op }) begin
                if (stalled_cycles == 0) begin
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("5 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                    PC = PC + 1;
                    stalled_cycles = 3;
                end else if (stalled_cycles == 2) begin
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("6 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                    stalled_cycles = stalled_cycles-1;
                end else if (stalled_cycles == 1) begin
                    if (instr_mem_vif.instr_mem[PC][15:12] == BR_op) begin
                        PC = PC + 1 + { {7{instr_mem_vif.instr_mem[PC][8]}}, instr_mem_vif.instr_mem[PC][8:0] };
                    end else if (instr_mem_vif.instr_mem[PC][15:12] == JMP_op) begin
                        PC = LC3_tb.dut.w.RF.register_files[instr_mem_vif.instr_mem[PC][8:6]];
                    end
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("7 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                end               
            end else if (instr_mem_vif.instr_mem[PC][15:12] inside { LD_op, LDR_op, ST_op, STR_op }) begin
                if (stalled_cycles == 0) begin
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("8 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                    PC = PC + 1;
                    stalled_cycles = 1;
                end else begin
                    if (tr.PC != PC) begin
                        `uvm_error("SCO", $sformatf("9 PC MISMATCH: EXPECTED: %04h, ACTUAL: %04h", PC, tr.PC));
                    end else begin
                        `uvm_info("SCO", "PC MATCH", UVM_NONE);
                    end
                    stalled_cycles = stalled_cycles-1;
                end
            end
        end
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
        for (int n = 0; n < 16; n++) begin
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
