`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit [1:0] { update_br_taken, update_br_nt_taken, no_update, rst } op_t;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
         op_t         op;
         logic        enable_updatePC;
         logic        enable_fetch;
    rand logic [15:0] taddr;
         logic        br_taken;
         logic [15:0] pc;
         logic [15:0] npc;
         logic Imem_rd;         
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

class branch_taken extends uvm_sequence#(transaction);
    `uvm_object_utils(branch_taken)
    
    transaction tr;
    
    function new(string name = "branch_taken");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = update_br_taken;
        `uvm_info("SEQ", $sformatf("MODE: BRANCH TAKEN, ADDR : %0d", tr.taddr), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class branch_not_taken extends uvm_sequence#(transaction);
    `uvm_object_utils(branch_not_taken)
    
    transaction tr;
    
    function new(string name = "branch_not_taken");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = update_br_nt_taken;
        `uvm_info("SEQ", $sformatf("MODE: BRANCH NOT TAKEN"), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class not_updated extends uvm_sequence#(transaction);
    `uvm_object_utils(not_updated)
    
    transaction tr;
    
    function new(string name = "not_updated");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = no_update;
        `uvm_info("SEQ", $sformatf("MODE: NO UPDATE"), UVM_NONE);        
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
        tr.op = rst;
        `uvm_info("SEQ", $sformatf("MODE: RESET"), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class seq_library extends uvm_sequence_library#(transaction);
    `uvm_object_utils(seq_library)
    `uvm_sequence_library_utils(seq_library)
    
    function new(string name = "seq_library");
        super.new(name);
        add_typewide_sequence(branch_taken::get_type());
        add_typewide_sequence(branch_not_taken::get_type());
        add_typewide_sequence(not_updated::get_type());
        add_typewide_sequence(reset::get_type());
    endfunction
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual fetch_if vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual fetch_if)::get(this,"","vif",vif))
            `uvm_error("DRV","Unable to access interface");
    endfunction
    
    task branch_taken();
        `uvm_info("DRV", $sformatf("MODE: BRANCH TAKEN, TADDR: %0d", tr.taddr), UVM_NONE);
        vif.rst             <= 1'b0;
        vif.enable_updatePC <= 1'b1;
        vif.enable_fetch    <= 1'b1;
        vif.taddr           <= tr.taddr;
        vif.br_taken        <= 1'b1;
        @(posedge vif.clk);
    endtask
    
    task branch_not_taken();
        `uvm_info("DRV", "MODE: BRANCH NOT TAKEN", UVM_NONE);
        vif.rst             <= 1'b0;
        vif.enable_updatePC <= 1'b1;
        vif.enable_fetch    <= 1'b1;
        vif.taddr           <= tr.taddr;
        vif.br_taken        <= 1'b0;
        @(posedge vif.clk);
    endtask
    
    task not_updated();
        `uvm_info("SEQ", "MODE: NO UPDATE", UVM_NONE);
        vif.rst             <= 1'b0; 
        vif.enable_updatePC <= 1'b0;
        vif.enable_fetch    <= 1'b0;
        vif.taddr           <= tr.taddr;
        vif.br_taken        <= 1'b0;
        @(posedge vif.clk);
    endtask
    
    task reset();
        `uvm_info("SEQ", $sformatf("MODE: RESET"), UVM_NONE);
        vif.rst             <= 1'b1; 
        vif.enable_updatePC <= 1'b0;
        vif.enable_fetch    <= 1'b0;
        vif.taddr           <= tr.taddr;
        vif.br_taken        <= 1'b0;
        @(posedge vif.clk);
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(tr);
            case(tr.op)
              update_br_taken:    branch_taken();
              update_br_nt_taken: branch_not_taken();
              no_update:          not_updated();
              rst:                reset();
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
    virtual fetch_if vif;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual fetch_if)::get(this,"","vif",vif))
            `uvm_error("MON", "Unable to access interface");
    endfunction    
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            tr.pc        = vif.pc;
            tr.npc       = vif.npc;
            tr.Imem_rd   = vif.Imem_rd;
            if (vif.rst) begin
                tr.op    = rst;
                `uvm_info("MON", $sformatf("SYSTEM RESET DETECTED: PC: %0h | NPC: %0h | Imem_rd: %0b",tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
            end else if (vif.br_taken) begin
                tr.op    = update_br_taken;
                tr.taddr = vif.taddr;
                `uvm_info("MON", $sformatf("BRANCH TAKEN: TADDR: %0 | PC: %0h | NPC: %0h | Imem_rd: %0b",tr.taddr,tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
            end else if (vif.enable_updatePC && vif.enable_fetch) begin
                tr.op    = update_br_nt_taken;
                `uvm_info("MON", $sformatf("BRANCH NOT TAKEN: PC: %0h | NPC: %0h | Imem_rd: %0b",tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
            end else begin
                tr.op    = no_update;
                `uvm_info("MON", $sformatf("NO UPDATE: PC: %0h | NPC: %0h | Imem_rd: %0b",tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);  
            end
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
    
    virtual function void write(transaction tr);
        if (tr.op == rst) begin       
            `uvm_info("SCO", $sformatf("SYSTEM RESET DETECTED: PC: %0h | NPC: %0h | Imem_rd: %0b",tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
        end else if (tr.op == update_br_taken) begin
            `uvm_info("SCO", $sformatf("BRANCH TAKEN: TADDR: %0 | PC: %0h | NPC: %0h | Imem_rd: %0b",tr.taddr,tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
        end else if (tr.op == update_br_nt_taken) begin
            `uvm_info("SCO", $sformatf("BRANCH NOT TAKEN: PC: %0h | NPC: %0h | Imem_rd: %0b",tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
        end else if (tr.op == no_update) begin
            `uvm_info("SCO", $sformatf("NO UPDATE: PC: %0h | NPC: %0h | Imem_rd: %0b",tr.pc,tr.npc,tr.Imem_rd), UVM_NONE);
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
    seq_library seqlib;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e      = environment::type_id::create("environment", this);
        seqlib = seq_library::type_id::create("seqlib", this);
        seqlib.selection_mode = UVM_SEQ_LIB_RANDC;
        seqlib.sequence_count = 25;
        seqlib.init_sequence_library();
        seqlib.print();
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        assert(seqlib.randomize());
        seqlib.start(e.a.seqr);
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module fetch_tb;
    fetch_if vif();
    
    fetch dut (
        .clk(vif.clk), 
        .rst(vif.rst),
        .enable_updatePC(vif.enable_updatePC),
        .enable_fetch(vif.enable_fetch),
        .taddr(vif.taddr),
        .br_taken(vif.br_taken),
        .pc(vif.pc),
        .npc(vif.npc),
        .Imem_rd(vif.Imem_rd)
    );
    
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual fetch_if)::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
