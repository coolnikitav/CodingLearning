`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit  {  } op_t;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
         
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

class  extends uvm_sequence#(transaction);
    `uvm_object_utils(reset)
    
    transaction tr;
    
    function new(string name = "reset");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);

        finish_item(tr);
    endtask
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
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);

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
            @(posedge vif.clk); #0.001;

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

    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e      = environment::type_id::create("environment", this);
   
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module LC3_tb;

    
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual )::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
