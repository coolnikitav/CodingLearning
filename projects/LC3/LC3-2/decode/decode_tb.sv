`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit [1:0] { 
    decode_op,
    no_update,
    rst
} op_t;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
         op_t         op;
         logic        enable_decode;
    rand logic [15:0] Instr_dout;
    rand logic [15:0] npc_in;
         logic [15:0] IR;
         logic [5:0]  E_Control;
         logic [1:0]  W_Control;
         logic        Mem_Control;
         logic [15:0] npc_out;
         
    function new(string name = "transaction");
        super.new(name);
    endfunction
    
    constraint Instr_dout_cntrl {
        Instr_dout[15:12] inside {
            4'b0001,  // ADD
            4'b0101,  // AND
            4'b1001,  // NOT
            4'b0000,  // BR
            4'b1100,  // JMP
            4'b0010,  // LD
            4'b0110,  // LDR
            4'b1010,  // LDI
            4'b1110,  // LEA
            4'b0011,  // ST
            4'b0111,  // STR
            4'b1011   // STI  
        };
    };
endclass

///////////////////////////////////////////////

class decode_enabled extends uvm_sequence#(transaction);
    `uvm_object_utils(decode_enabled)
    
    transaction tr;
    
    function new(string name = "decode_enable");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize());
        tr.op            = decode_op;
        tr.enable_decode = 1'b1;
        `uvm_info("SEQ", $sformatf("MODE: DECODE_ENABLED: Instr_dout: %0b npc_in: %0h", tr.Instr_dout, tr.npc_in), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class decode_not_enabled extends uvm_sequence#(transaction);
    `uvm_object_utils(decode_not_enabled)
    
    transaction tr;
    
    function new(string name = "decode_not_enabled");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize());
        tr.op            = no_update;
        tr.enable_decode = 1'b0;
        `uvm_info("SEQ", "MODE: DECODE_NOT_ENABLED", UVM_NONE);
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
        assert(tr.randomize());
        tr.op            = rst;
        `uvm_info("SEQ", "MODE: RESET", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual decode_if vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual decode_if)::get(this,"","vif",vif))
            `uvm_error("DRV","Unable to access interface");
    endfunction
    
    task decode_enabled();
        vif.rst           <= 1'b0;
        vif.enable_decode <= tr.enable_decode;
        vif.Instr_dout    <= tr.Instr_dout;
        vif.npc_in        <= tr.npc_in;
        @(posedge vif.clk);
        `uvm_info("DRV", $sformatf("MODE: DECODE ENABLED: Instr_dout: %0b npc_in: %0h", tr.Instr_dout, tr.npc_in), UVM_NONE); #0.002;
    endtask
    
    task decode_not_enabled();
        vif.rst           <= 1'b0;
        vif.enable_decode <= tr.enable_decode;
        vif.Instr_dout    <= tr.Instr_dout;
        vif.npc_in        <= tr.npc_in;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: DECODE_NOT_ENABLED", UVM_NONE); #0.002;
    endtask
    
    task reset();
        vif.rst           <= 1'b1;
        vif.enable_decode <= 1'b0;
        vif.Instr_dout    <= tr.Instr_dout;
        vif.npc_in        <= tr.npc_in;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: RESET", UVM_NONE); #0.002;
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            case(tr.op)
                decode_op: decode_enabled();
                no_update: decode_not_enabled();
                rst:       reset();
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
    virtual decode_if vif;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual decode_if)::get(this,"","vif",vif))
            `uvm_error("MON", "Unable to access interface");
    endfunction    
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk); #0.001;
            tr.Instr_dout  = vif.Instr_dout;
            tr.npc_in      = vif.npc_in;
            tr.IR          = vif.IR;
            tr.E_Control   = vif.E_Control;
            tr.W_Control   = vif.W_Control;
            tr.Mem_Control = vif.Mem_Control;
            tr.npc_out     = vif.npc_out;
            if (vif.rst) begin
                tr.op = rst;
                `uvm_info("MON", $sformatf("RESET: IR: %0b | E_Control: %0b | W_Control: %0h | Mem_Control: %0h | npc_out: %0h", tr.IR, tr.E_Control, tr.W_Control, tr.Mem_Control, tr.npc_out), UVM_NONE);
            end else if (vif.enable_decode) begin
                tr.op = decode_op;
                `uvm_info("MON", $sformatf("INSTRUCTION DECODE: IR: %0b | E_Control: %0b | W_Control: %0h | Mem_Control: %0h | npc_out: %0h", tr.IR, tr.E_Control, tr.W_Control, tr.Mem_Control, tr.npc_out), UVM_NONE);
            end else begin
                tr.op = no_update;
                `uvm_info("MON", $sformatf("NO UPDATE: IR: %0b | E_Control: %0b | W_Control: %0h | Mem_Control: %0h | npc_out: %0h", tr.IR, tr.E_Control, tr.W_Control, tr.Mem_Control, tr.npc_out), UVM_NONE);
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
    
    function logic [5:0] golden_e_control (input bit [15:0] Instr_dout);
        case (Instr_dout[15:12])
            4'b0001: begin
                if (Instr_dout[5])  
                    return 6'b000000;   //ADD_REG
                else
                    return 6'b000001;   //ADD_IMM
            end
            4'b0101: begin
                if (Instr_dout[5])
                    return 6'b010000;   // AND_REG
                else 
                    return 6'b010001;   // AND_IMM
            end
            4'b1001: return 6'b100000;  // NOT
            4'b0000: return 6'b000110;  // BR
            4'b1100: return 6'b001100;  // JMP
            4'b0010: return 6'b000110;  // LD
            4'b0110: return 6'b001000;  // LDR
            4'b1010: return 6'b000110;  // LDI
            4'b1110: return 6'b000110;  // LEA
            4'b0011: return 6'b000110;  // ST
            4'b0111: return 6'b001000;  // STR
            4'b1011: return 6'b000110;  // STI 
        endcase
    endfunction
    
    function logic [1:0] golden_w_control (input bit [15:0] Instr_dout);
        case(Instr_dout[15:12])
            4'b0001: return 2'h0;  // ADD
            4'b0101: return 2'h0;  // AND
            4'b1001: return 2'h0;  // NOT
            4'b0000: return 2'h0;  // BR
            4'b1100: return 2'h0;  // JMP
            4'b0010: return 2'h1;  // LD
            4'b0110: return 2'h1;  // LDR
            4'b1010: return 2'h1;  // LDI
            4'b1110: return 2'h2;  // LEA
            4'b0011: return 2'h0;  // ST
            4'b0111: return 2'h0;  // STR
            4'b1011: return 2'h0;  // STI     
        endcase
    endfunction
    
    function logic golden_mem_control (input bit [15:0] Instr_dout);
        case(Instr_dout[15:12])
            4'b0001: return 1'h0;  // ADD
            4'b0101: return 1'h0;  // AND
            4'b1001: return 1'h0;  // NOT
            4'b0000: return 1'h0;  // BR
            4'b1100: return 1'h0;  // JMP
            4'b0010: return 1'h0;  // LD
            4'b0110: return 1'h0;  // LDR
            4'b1010: return 1'h1;  // LDI
            4'b1110: return 1'h0;  // LEA
            4'b0011: return 1'h0;  // ST
            4'b0111: return 1'h0;  // STR
            4'b1011: return 1'h1;  // STI     
        endcase
    endfunction
     
    virtual function void write(transaction tr);        
        if (tr.op == rst) begin
            if (tr.IR          == 16'h0 &&
                tr.E_Control   == 6'h0 &&
                tr.W_Control   == 2'h0 &&
                tr.Mem_Control == 1'h0 &&
                tr.npc_out     == 16'h0) begin
                `uvm_info("SCO", "DATA MATCH", UVM_NONE);
            end else begin
                `uvm_error("SCO", "DATA MISMATCH");
            end
        end else if (tr.op == decode_op) begin
            `uvm_info("SCO", $sformatf("INSTRUCTION DECODE: Instr_dout: %0b | golden_e_control: %0b | golden_w_control: %0h | golden_mem_Control: %0h | npc_in: %0h", tr.Instr_dout, golden_e_control(tr.Instr_dout), golden_w_control(tr.Instr_dout), golden_mem_control(tr.Instr_dout), tr.npc_in), UVM_NONE);
            if (tr.IR          == tr.Instr_dout &&
                tr.E_Control   == golden_e_control(tr.Instr_dout) &&
                tr.W_Control   == golden_w_control(tr.Instr_dout) &&
                tr.Mem_Control == golden_mem_control(tr.Instr_dout) &&
                tr.npc_out     == tr.npc_in) begin
                `uvm_info("SCO", "DATA MATCH", UVM_NONE);
            end else begin
                `uvm_error("SCO", "DATA MISMATCH");
            end
        end else if (tr.op == no_update) begin
            `uvm_info("SCO", "NO UPDATE", UVM_NONE);
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
    
    environment        e;
    decode_enabled     d_e;
    decode_not_enabled d_n_e;
    reset              r;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e     = environment::type_id::create("environment", this);
        d_e   = decode_enabled::type_id::create("d_e");
        d_n_e = decode_not_enabled::type_id::create("d_n_e");
        r     = reset::type_id::create("r");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        r.start(e.a.seqr);  // reset dut to start
        for (int i = 0; i < 100; i++) begin
            case($urandom_range(2))
                2'h0: d_e.start(e.a.seqr);
                2'h1: d_n_e.start(e.a.seqr);
                2'h2: r.start(e.a.seqr);
            endcase
        end
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module decode_tb;
    decode_if vif();
    
    decode dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .enable_decode(vif.enable_decode),
        .Instr_dout(vif.Instr_dout),
        .npc_in(vif.npc_in),
        .IR(vif.IR),
        .E_Control(vif.E_Control),
        .W_Control(vif.W_Control),
        .Mem_Control(vif.Mem_Control),
        .npc_out(vif.npc_out)
    );
    
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual decode_if)::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
