`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit [1:0] { 
    alu_instr_op,  // 6 ALU instructions,
    control_instr_op,  // ALU, LEA, JMP sequence
    mem_instr_op,  // ALU, LEA, LDI, ALU, ALU sequence
    reset_op
} op_t;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
    op_t         op;
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
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

class alu_instr extends uvm_sequence#(transaction);
    `uvm_object_utils(alu_instr)
    
    transaction tr;
    
    function new(string name = "alu_instr");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        tr.op = alu_instr_op;
        `uvm_info("SEQ", "MODE: ALU INSTR", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class control_instr extends uvm_sequence#(transaction);
    `uvm_object_utils(control_instr)
    
    transaction tr;
    
    function new(string name = "control_instr");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        tr.op = control_instr_op;
        `uvm_info("SEQ", "MODE: CONTROL INSTR", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class mem_instr extends uvm_sequence#(transaction);
    `uvm_object_utils(mem_instr)
    
    transaction tr;
    
    function new(string name = "mem_instr");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        tr.op = mem_instr_op;   
        `uvm_info("SEQ", "MODE: MEM INSTR", UVM_NONE);     
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
        tr.op = reset_op;
        `uvm_info("SEQ", "MODE: RESET", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual controller_if vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual controller_if)::get(this,"","vif",vif))
            `uvm_error("DRV","Unable to access interface");
    endfunction
    
    task print_inputs();
        `uvm_info("DRV", $sformatf("rst: %01b, complete_data: %01b, complete_instr: %01b, IR: %04h, NZP: %03b, psr: %03b, IR_Exec: %04h, IMem_dout: %04h",
                                    vif.rst,
                                    vif.complete_data,
                                    vif.complete_instr,
                                    vif.IR,
                                    vif.NZP,
                                    vif.psr,
                                    vif.IR_Exec,
                                    vif.IMem_dout), UVM_NONE);
    endtask
    
    task alu_instr();
        vif.rst            <= 1'b0; 
        vif.complete_data  <= 1'b0;  // no memory access instructions in this sequence
        vif.complete_instr <= 1'b0;
        vif.NZP            <= 3'b0;  // no BR instructions in this sequence
        vif.psr            <= 3'b010;
        @(posedge vif.clk);
        print_inputs();
        vif.complete_instr <= 1'b1;
        vif.IMem_dout      <= 16'h5020;
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'h1027;
        vif.IR             <= 16'h5020;
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'h5260;
        vif.IR             <= 16'h1027;
        vif.IR_Exec        <= 16'h5020;
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'h1265;
        vif.IR             <= 16'h5260;
        vif.IR_Exec        <= 16'h1027;
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'h103F;
        vif.IR             <= 16'h1265;
        vif.IR_Exec        <= 16'h5260;
        vif.psr            <= 3'b010;  // result of R0 & 0 is zero
        @(posedge vif.clk);
        print_inputs();
        vif.complete_instr <= 1'b0;
        vif.IMem_dout      <= 16'h1401;
        vif.IR             <= 16'h103F;
        vif.IR_Exec        <= 16'h1265;
        vif.psr            <= 3'b001;  // result of R0 + 7 is positive
        @(posedge vif.clk);
        print_inputs();
        vif.IR             <= 16'h1401;
        vif.IR_Exec        <= 16'h103F;
        vif.psr            <= 3'b010;  // result of R1 & 0 is zero
        @(posedge vif.clk);
        print_inputs();
        vif.IR_Exec        <= 16'h1401;
        vif.psr            <= 3'b001;  // result of R1 + 5 is positive
        @(posedge vif.clk);
        print_inputs();
        vif.psr            <= 3'b100;  // result of R0 - 1 is negative
        @(posedge vif.clk);
        print_inputs();
        vif.psr            <= 3'b001;  // result of R0 + R1 is positive
        @(posedge vif.clk);
        print_inputs(); #0.002;
    endtask
    
    task control_instr();
        vif.rst            <= 1'b0; 
        vif.complete_data  <= 1'b0;  // no memory access instructions in this sequence
        vif.complete_instr <= 1'b0;
        vif.NZP            <= 3'b0;  // no BR instructions in this sequence
        vif.psr            <= 3'b010;
        @(posedge vif.clk);
        print_inputs();
        vif.complete_instr <= 1'b1;
        vif.IMem_dout      <= 16'hEC04;
        @(posedge vif.clk); 
        print_inputs();       
        vif.IMem_dout      <= 16'hC180;
        vif.IR             <= 16'hEC04;
        @(posedge vif.clk);
        print_inputs();
        vif.complete_instr <= 1'b0;
        vif.IR             <= 16'hC180;
        vif.IR_Exec        <= 16'hEC04;
        @(posedge vif.clk);
        print_inputs();
        vif.IR_Exec        <= 16'hC180;
        vif.psr            <= 3'b001;  // result of PC + sxt(9'h004) is positive
        @(posedge vif.clk);
        print_inputs(); #0.002;
    endtask
    
    task mem_instr();
        vif.rst            <= 1'b0; 
        vif.complete_data  <= 1'b0;
        vif.complete_instr <= 1'b0;
        vif.NZP            <= 3'b0;  // no BR instructions in this sequence
        vif.psr            <= 3'b010;
        @(posedge vif.clk);
        print_inputs();
        vif.complete_instr <= 1'b1;
        vif.IMem_dout      <= 16'hEC04;        
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'hA7FA;
        vif.IR             <= 16'hEC04;
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'h14A1;
        vif.IR             <= 16'hA7FA;
        vif.IR_Exec        <= 16'hEC04;
        @(posedge vif.clk);
        print_inputs();
        vif.psr            <= 3'b001;  // result of PC + sxt('9'h004)
        vif.IMem_dout      <= 16'h5020;
        vif.IR             <= 16'h14A1;
        vif.IR_Exec        <= 16'hA7FA;
        @(posedge vif.clk);
        print_inputs();
        vif.IMem_dout      <= 16'h5020;
        vif.IR             <= 16'h14A1;
        @(posedge vif.clk);
        print_inputs();
        vif.complete_data  <= 1'b1;
        vif.IMem_dout      <= 16'h5020;
        vif.IR             <= 16'h14A1;
        @(posedge vif.clk);
        print_inputs();
        vif.complete_data  <= 1'b0;
        vif.complete_instr <= 1'b0;
        vif.psr            <= 3'b010;  // R3 hasn't been written to yet
        vif.IMem_dout      <= 16'h5260;
        vif.IR             <= 16'h5020;
        vif.IR_Exec        <= 16'hEC04;
        @(posedge vif.clk);
        print_inputs(); #0.002;
    endtask
    
    task reset();
        vif.rst            <= 1'b1;
        vif.complete_data  <= 1'b0;
        vif.complete_instr <= 1'b0;
        vif.IR             <= 1'b0;
        vif.NZP            <= 1'b0;
        vif.psr            <= 1'b0;
        vif.IR_Exec        <= 1'b0;
        vif.IMem_dout      <= 1'b0;
        repeat(5) @(posedge vif.clk);
        print_inputs(); #0.002;
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            case(tr.op)
                alu_instr_op:     alu_instr();
                control_instr_op: control_instr();
                mem_instr_op:     mem_instr();
                reset_op:         reset();
            endcase
            seq_item_port.item_done();
        end
    endtask
endclass

///////////////////////////////////////////////

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) send;
    transaction tr;
    virtual controller_if vif;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual controller_if)::get(this,"","vif",vif))
            `uvm_error("MON", "Unable to access interface");
    endfunction    
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk); #0.001;
            tr.enable_updatePC  = vif.enable_updatePC;
            tr.enable_fetch     = vif.enable_fetch;
            tr.enable_decode    = vif.enable_decode;
            tr.enable_execute   = vif.enable_execute;
            tr.enable_writeback = vif.enable_writeback;
            tr.br_taken         = vif.br_taken;
            tr.bypass_alu_1     = vif.bypass_alu_1;
            tr.bypass_alu_2     = vif.bypass_alu_2;
            tr.bypass_mem_1     = vif.bypass_mem_1;
            tr.bypass_mem_2     = vif.bypass_mem_2;
            tr.mem_state        = vif.mem_state;
            `uvm_info("MON", $sformatf("enable_updatePC: %01b, enable_fetch: %01b, enable_decode: %01b, enable_execute: %01b, enable_writeback: %01b, br_taken: %01b, bypass_alu_1: %01b, bypass_alu_2: %01b, bypass_mem_1: %01b, bypass_mem_2: %01b, mem_state: %01b",
                                        tr.enable_updatePC,
                                        tr.enable_fetch,
                                        tr.enable_decode,
                                        tr.enable_execute,
                                        tr.enable_writeback,
                                        tr.br_taken,
                                        tr.bypass_alu_1,
                                        tr.bypass_alu_2,
                                        tr.bypass_mem_1,
                                        tr.bypass_mem_2,
                                        tr.mem_state), UVM_NONE);
            send.write(tr);
        end
    endtask
endclass

///////////////////////////////////////////////

class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(scoreboard)
    
    uvm_analysis_imp#(transaction, scoreboard) recv;
    
    function new(input string inst = "scoreboard", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
    endfunction        
   
    task compare_alu_instr();
        
    endtask
    
    task compare_control_instr();
    
    endtask
    
    task compare_mem_instr();
    
    endtask
    
    task compare_reset();
    
    endtask
     
    virtual function void write(transaction tr);
        
        //$display("---------------------------------------------");
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
    
    environment   e;
    alu_instr     a_i;
    control_instr c_i;
    mem_instr     m_i;
    reset         r;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e   = environment::type_id::create("environment", this);
        a_i = alu_instr::type_id::create("a_i");
        c_i = control_instr::type_id::create("c_i");
        m_i = mem_instr::type_id::create("m_i");
        r   = reset::type_id::create("r");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        r.start(e.a.seqr);
        a_i.start(e.a.seqr);
        r.start(e.a.seqr);
        c_i.start(e.a.seqr);
        r.start(e.a.seqr);
        m_i.start(e.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module controller_tb;
    controller_if vif();
    
    controller dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .complete_data(vif.complete_data),
        .complete_instr(vif.complete_instr),
        .IR(vif.IR),
        .NZP(vif.NZP),
        .psr(vif.psr),
        .IR_Exec(vif.IR_Exec),
        .IMem_dout(vif.IMem_dout),
        .enable_updatePC(vif.enable_updatePC),
        .enable_fetch(vif.enable_fetch),
        .enable_decode(vif.enable_decode),
        .enable_execute(vif.enable_execute),
        .enable_writeback(vif.enable_writeback),
        .br_taken(vif.br_taken),
        .bypass_alu_1(vif.bypass_alu_1),
        .bypass_alu_2(vif.bypass_alu_2),
        .bypass_mem_1(vif.bypass_mem_1),
        .bypass_mem_2(vif.bypass_mem_2),
        .mem_state(vif.mem_state)
    );
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual controller_if)::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
