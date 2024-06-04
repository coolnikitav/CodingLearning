`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit [2:0]{ 
    aluout_op,     
    memout_op,
    pcout_op,
    no_update_op,
    reset_op
} op_t;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
         op_t         op;
         logic        enable_writeback;
    rand logic [15:0] aluout;        
    rand logic [15:0] memout;
    rand logic [15:0] pcout;
         logic [1:0]  W_Control;
         logic [15:0] VSR1;
         logic [15:0] VSR2;
    rand logic [2:0]  dr;
    rand logic [2:0]  sr1;
    rand logic [2:0]  sr2;
         logic [2:0]  psr; 
         logic [15:0] golden_reg_file [7:0];   
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

class aluout extends uvm_sequence#(transaction);
    `uvm_object_utils(aluout)
    
    transaction tr;
    
    function new(string name = "aluout");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = aluout_op;
        tr.W_Control = 2'h0;
        `uvm_info("SEQ", $sformatf("MODE: ALUOUT: aluout: %04h | dr: %01h | sr1: %01h | sr2: %01h",
                                                  tr.aluout,
                                                  tr.dr,
                                                  tr.sr1,
                                                  tr.sr2), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class memout extends uvm_sequence#(transaction);
    `uvm_object_utils(memout)
    
    transaction tr;
    
    function new(string name = "memout");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = memout_op;
        tr.W_Control = 2'h1;
        `uvm_info("SEQ", $sformatf("MODE: MEMOUT: memout: %04h | dr: %01h | sr1: %01h | sr2: %01h",
                                                  tr.memout,
                                                  tr.dr,
                                                  tr.sr1,
                                                  tr.sr2), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class pcout extends uvm_sequence#(transaction);
    `uvm_object_utils(pcout)
    
    transaction tr;
    
    function new(string name = "pcout");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = pcout_op;
        tr.W_Control = 2'h2;
        `uvm_info("SEQ", $sformatf("MODE: PCOUT: pcout: %04h | dr: %01h | sr1: %01h | sr2: %01h",
                                                 tr.pcout,
                                                 tr.dr,
                                                 tr.sr1,
                                                 tr.sr2), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class no_update extends uvm_sequence#(transaction);
    `uvm_object_utils(no_update)
    
    transaction tr;
    
    function new(string name = "no_update");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = no_update_op;
        `uvm_info("SEQ", $sformatf("MODE: WRITEBACK NOT ENABLED: sr1: %01h | sr2: %01h", 
                                                                 tr.sr1,
                                                                 tr.sr2), UVM_NONE);
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
        `uvm_info("SEQ", "MODE: RESET", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual writeback_if vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual writeback_if)::get(this,"","vif",vif))
            `uvm_error("DRV","Unable to access interface");
    endfunction
    
    task aluout();
        vif.rst              <= 1'b0;
        vif.enable_writeback <= 1'b1;
        vif.aluout           <= tr.aluout;        
        vif.memout           <= tr.memout;
        vif.pcout            <= tr.pcout;
        vif.W_Control        <= tr.W_Control;
        vif.dr               <= tr.dr;
        vif.sr1              <= tr.sr1;
        vif.sr2              <= tr.sr2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: ALUOUT", UVM_NONE); #0.002;
    endtask
    
    task memout();
        vif.rst              <= 1'b0;
        vif.enable_writeback <= 1'b1;
        vif.aluout           <= tr.aluout;        
        vif.memout           <= tr.memout;
        vif.pcout            <= tr.pcout;
        vif.W_Control        <= tr.W_Control;
        vif.dr               <= tr.dr;
        vif.sr1              <= tr.sr1;
        vif.sr2              <= tr.sr2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: MEMOUT", UVM_NONE); #0.002;
    endtask
    
    task pcout();
        vif.rst              <= 1'b0;
        vif.enable_writeback <= 1'b1;
        vif.aluout           <= tr.aluout;        
        vif.memout           <= tr.memout;
        vif.pcout            <= tr.pcout;
        vif.W_Control        <= tr.W_Control;
        vif.dr               <= tr.dr;
        vif.sr1              <= tr.sr1;
        vif.sr2              <= tr.sr2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: PCOUT", UVM_NONE); #0.002;
    endtask
    
    task no_update();
        vif.rst              <= 1'b0;
        vif.enable_writeback <= 1'b0;
        vif.aluout           <= tr.aluout;        
        vif.memout           <= tr.memout;
        vif.pcout            <= tr.pcout;
        vif.W_Control        <= 1'b0;
        vif.dr               <= tr.dr;
        vif.sr1              <= tr.sr1;
        vif.sr2              <= tr.sr2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: WRITEBACK NOT ENABLED", UVM_NONE); #0.002;
    endtask
    
    task reset();
        vif.rst              <= 1'b1;
        vif.enable_writeback <= 1'b0;
        vif.aluout           <= tr.aluout;        
        vif.memout           <= tr.memout;
        vif.pcout            <= tr.pcout;
        vif.W_Control        <= 1'b0;
        vif.dr               <= tr.dr;
        vif.sr1              <= tr.sr1;
        vif.sr2              <= tr.sr2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: RESET", UVM_NONE); #0.002;
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            case(tr.op)
                aluout_op:    aluout();
                memout_op:    memout();
                pcout_op:     pcout();
                no_update_op: no_update();
                reset_op:     reset();
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
    virtual writeback_if vif;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual writeback_if)::get(this,"","vif",vif))
            `uvm_error("MON", "Unable to access interface");
    endfunction    
    
    task reset_golden_reg_file();
        for (int i = 0; i < 8; i++) begin
                tr.golden_reg_file[i] = 16'h0;
        end
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin  
            @(posedge vif.clk); #0.001;
            tr.VSR1 = vif.VSR1;
            tr.VSR2 = vif.VSR2;
            tr.enable_writeback = vif.enable_writeback;
            tr.aluout = vif.aluout;
            tr.memout = vif.memout;
            tr.pcout = vif.pcout;
            tr.sr1 = vif.sr1;
            tr.sr2 = vif.sr2;
            tr.dr = vif.dr;
            if (tr.enable_writeback) begin
                tr.W_Control = vif.W_Control;
                case(tr.W_Control)
                    2'h0: tr.golden_reg_file[tr.dr] = tr.aluout;
                    2'h1: tr.golden_reg_file[tr.dr] = tr.memout;
                    2'h2: tr.golden_reg_file[tr.dr] = tr.pcout;
                endcase
            end         
            tr.psr  = vif.psr;
            if (vif.rst) begin
                tr.op = reset_op;
                reset_golden_reg_file();
                `uvm_info("MON", $sformatf("MODE: RESET: VSR1: %04h | VSR2: %04h | psr: %03b",
                                                          tr.VSR1,
                                                          tr.VSR2,
                                                          tr.psr), UVM_NONE);
            end else if (~vif.enable_writeback) begin
                tr.op = no_update_op;
                `uvm_info("MON", $sformatf("MODE: WRITEBACK NOT ENABLED: VSR1: %04h | VSR2: %04h",
                                                          tr.VSR1,
                                                          tr.VSR2), UVM_NONE);
            end else if (vif.W_Control == 2'h0) begin
                tr.op = aluout_op;
                `uvm_info("MON", $sformatf("MODE: ALUOUT: VSR1: %04h | VSR2: %04h | psr: %03b",
                                                          tr.VSR1,
                                                          tr.VSR2,
                                                          tr.psr), UVM_NONE);
            end else if (vif.W_Control == 2'h1) begin
                tr.op = memout_op;
                `uvm_info("MON", $sformatf("MODE: MEMOUT: VSR1: %04h | VSR2: %04h | psr: %03b",
                                                          tr.VSR1,
                                                          tr.VSR2,
                                                          tr.psr), UVM_NONE);
            end else if (vif.W_Control == 2'h2) begin
                tr.op = pcout_op;
                `uvm_info("MON", $sformatf("MODE: PCOUT: VSR1: %04h | VSR2: %04h | psr: %03b",
                                                          tr.VSR1,
                                                          tr.VSR2,
                                                          tr.psr), UVM_NONE);
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
    
    function logic [2:0] golden_psr(input bit [15:0] DR_in);
        if (!DR_in) begin              // zero
            return 3'b010;
        end else if (DR_in[15]) begin  // negative
            return 3'b100;
        end else begin                 // positive
            return 3'b001; 
        end
    endfunction
    
    virtual function void write(transaction tr);     
        if (tr.VSR1 == tr.golden_reg_file[tr.sr1]) begin
            if (tr.VSR2 == tr.golden_reg_file[tr.sr2]) begin
                if (tr.psr  == (tr.op == no_update_op ? tr.psr : (tr.op == reset_op ? 3'b000 : golden_psr(tr.golden_reg_file[tr.dr])))) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);
                end else begin
                    `uvm_error("SCO", "PSR MISMATCH");
                end
            end else begin
                `uvm_error("SCO", "VSR2 MISMATCH");
            end
        end else begin
            `uvm_error("SCO", "VSR1 MISMATCH");
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
    aluout      a;
    memout      m;
    pcout       p;
    no_update   n_u;
    reset       r;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e   = environment::type_id::create("environment", this);
        a   = aluout::type_id::create("aluout", this);
        m   = memout::type_id::create("memout", this);
        p   = pcout::type_id::create("pcout", this);
        n_u = no_update::type_id::create("no_udpate", this);
        r   = reset::type_id::create("reset", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        r.start(e.a.seqr);  // reset dut to start
        for (int i = 0; i < 100; i++) begin
            case($urandom_range(4))
                4'h0: a.start(e.a.seqr);
                4'h1: m.start(e.a.seqr);
                4'h2: p.start(e.a.seqr);
                4'h3: n_u.start(e.a.seqr);
                4'h4: r.start(e.a.seqr);
            endcase
        end
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module writeback_tb;
    writeback_if vif();
    
    writeback dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .enable_writeback(vif.enable_writeback),
        .aluout(vif.aluout),        
        .memout(vif.memout),
        .pcout(vif.pcout),
        .W_Control(vif.W_Control),
        .VSR1(vif.VSR1),
        .VSR2(vif.VSR2),
        .dr(vif.dr),
        .sr1(vif.sr1),
        .sr2(vif.sr2),
        .psr(vif.psr)
    );
    
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual writeback_if)::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
