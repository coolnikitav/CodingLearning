`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit [2:0] {  
    read_mem_i_op,   // READ_MEM with M_Control = 1
    read_mem_d_op,   // READ_MEM with M_Control = 0
    read_mem_indir_op,
    write_mem_i_op,  // WRITE_MEM with M_Control = 1
    write_mem_d_op,  // WRITE_MEM with M_Control = 0
    init_state_op
} op_t;

///////////////////////////////////////////////

localparam READ_MEM = 2'h0,
           READ_MEM_INDIR = 2'h1,
           WRITE_MEM = 2'h2,
           INIT_STATE = 2'h3;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
         op_t         op;
         logic [1:0]  mem_state;
         logic        M_Control;
    rand logic [15:0] M_Data;
    rand logic [15:0] M_Addr;  
    rand logic [15:0] DMem_dout;
         logic [15:0] DMem_addr;
         logic        DMem_rd;
         logic [15:0] DMem_din;
         logic [15:0] memout; 
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

task print_inputs(string oper, transaction tr);
    `uvm_info("SEQ", $sformatf("MODE: %0s: M_Data: %04h | M_Addr: %04h | DMem_dout: %04h", 
                                      oper,
                                      tr.M_Data, 
                                      tr.M_Addr,
                                      tr.DMem_dout), UVM_NONE);
endtask

///////////////////////////////////////////////

class read_mem_i extends uvm_sequence#(transaction);
    `uvm_object_utils(read_mem_i)
    
    transaction tr;
    
    function new(string name = "read_mem_i");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = read_mem_i_op;
        tr.mem_state = READ_MEM;
        tr.M_Control = 1'b1;
        print_inputs("READ_MEM_I", tr);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class read_mem_d extends uvm_sequence#(transaction);
    `uvm_object_utils(read_mem_d)
    
    transaction tr;
    
    function new(string name = "read_mem_d");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = read_mem_d_op;
        tr.mem_state = READ_MEM;
        tr.M_Control = 1'b0;
        print_inputs("READ_MEM_D", tr);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class read_mem_indir extends uvm_sequence#(transaction);
    `uvm_object_utils(read_mem_indir)
    
    transaction tr;
    
    function new(string name = "read_mem_indir");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = read_mem_indir_op;
        tr.mem_state = READ_MEM_INDIR;
        tr.M_Control = 1'b0;
        print_inputs("READ_MEM_INDIR", tr);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class write_mem_i extends uvm_sequence#(transaction);
    `uvm_object_utils(write_mem_i)
    
    transaction tr;
    
    function new(string name = "write_mem_i");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = write_mem_i_op;
        tr.mem_state = WRITE_MEM;
        tr.M_Control = 1'b1;
        print_inputs("WRITE_MEM_I", tr);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class write_mem_d extends uvm_sequence#(transaction);
    `uvm_object_utils(write_mem_d)
    
    transaction tr;
    
    function new(string name = "write_mem_d");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = write_mem_d_op;
        tr.mem_state = WRITE_MEM;
        tr.M_Control = 1'b0;
        print_inputs("WRITE_MEM_D", tr);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class init_state extends uvm_sequence#(transaction);
    `uvm_object_utils(init_state)
    
    transaction tr;
    
    function new(string name = "init_state");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = init_state_op;
        tr.mem_state = INIT_STATE;
        tr.M_Control = 1'b0;
        print_inputs("INIT_STATE", tr);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual memaccess_if vif;
    transaction tr;
    
    event drvnext;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual memaccess_if)::get(this,"","vif",vif))
            `uvm_error("DRV","Unable to access interface");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            vif.mem_state = tr.mem_state;
            vif.M_Control = tr.M_Control;
            vif.M_Data    = tr.M_Data;
            vif.M_Addr    = tr.M_Addr;        
            vif.DMem_dout = tr.DMem_dout;
            -> drvnext;
            `uvm_info("DRV", $sformatf("MODE: %0s", tr.op.name), UVM_NONE);
            seq_item_port.item_done();
        end
    endtask
endclass

///////////////////////////////////////////////

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) send;
    transaction tr;
    virtual memaccess_if vif;
    
    event drvnext;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual memaccess_if)::get(this,"","vif",vif))
            `uvm_error("MON", "Unable to access interface");
    endfunction    
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(drvnext); #0;
            tr.M_Data    = vif.M_Data;
            tr.M_Addr    = vif.M_Addr;  
            tr.DMem_dout = vif.DMem_dout;
            tr.DMem_addr = vif.DMem_addr;
            tr.DMem_rd   = vif.DMem_rd;
            tr.DMem_din  = vif.DMem_din;
            tr.memout    = vif.memout;
            case (vif.mem_state)
                READ_MEM:       tr.op = vif.M_Control == 1'b1 ? read_mem_i_op : read_mem_d_op;
                READ_MEM_INDIR: tr.op = read_mem_indir_op;
                WRITE_MEM:      tr.op = vif.M_Control == 1'b1 ? write_mem_i_op : write_mem_d_op;
                INIT_STATE:     tr.op = init_state_op;
            endcase    
            `uvm_info("MON", $sformatf("MODE: %0s: DMem_addr: %04h | DMem_rd: %01b | DMem_din: %04h | memout: %04h",
                                              tr.op.name,
                                              tr.DMem_addr,
                                              tr.DMem_rd,
                                              tr.DMem_din,
                                              tr.memout), UVM_NONE);      
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
    
    function void compare(input transaction tr, [16:0] DMem_dout, DMem_rd, [16:0] DMem_din, [16:0] memout);
        if (tr.DMem_addr === DMem_dout) begin
            if (tr.DMem_rd === DMem_rd) begin
                if (tr.DMem_din === DMem_din) begin
                    if (tr.memout === memout) begin
                        `uvm_info("SCO", "DATA MATCH", UVM_NONE);
                    end else begin
                        `uvm_error("SCO", "memout MISMATCH");
                    end
                end else begin
                    `uvm_error("SCO", "DMem_din MISMATCH");                            
                end
            end else begin
                `uvm_error("SCO", "DMem_rd MISMATCH");
            end
        end else begin
            `uvm_error("SCO", "DMem_addr MISMATCH");
        end
    endfunction
    
    virtual function void write(transaction tr);
        case (tr.op)
            read_mem_i_op: begin
                compare(tr, tr.DMem_dout, 1'b1, 16'b0, tr.DMem_dout);
            end
            read_mem_d_op: begin
                compare(tr, tr.M_Addr, 1'b1, 16'b0, tr.DMem_dout);
            end
            read_mem_indir_op: begin
                compare(tr, tr.M_Addr, 1'b1, 16'b0, tr.DMem_dout);
            end
            write_mem_i_op: begin
                compare(tr, tr.DMem_dout, 1'b0, tr.M_Data, 16'b0);
            end
            write_mem_d_op: begin
                compare(tr, tr.M_Addr, 1'b0, tr.M_Data, 16'b0);
            end
            init_state_op: begin
                compare(tr, 16'bz, 1'bz, 16'bz, 16'b0);
            end
        endcase    
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
    
    event drvnext;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m = monitor::type_id::create("m", this);
        d = driver::type_id::create("d", this);
        d.drvnext = drvnext;
        m.drvnext = drvnext;
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
    read_mem_i r_m_i;
    read_mem_d r_m_d;
    read_mem_indir r_m_indir;
    write_mem_i w_m_i;
    write_mem_d w_m_d;
    init_state i_s;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e         = environment::type_id::create("environment", this);
        r_m_i     = read_mem_i::type_id::create("r_m_i");
        r_m_d     = read_mem_d::type_id::create("r_m_d");
        r_m_indir = read_mem_indir::type_id::create("r_m_indir");
        w_m_i     = write_mem_i::type_id::create("w_m_i");
        w_m_d     = write_mem_d::type_id::create("w_m_d");
        i_s       = init_state::type_id::create("i_s");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        for (int i = 0; i < 100; i++) begin
            case ($urandom_range(5))
                4'h0: r_m_i.start(e.a.seqr);
                4'h1: r_m_d.start(e.a.seqr);
                4'h2: r_m_indir.start(e.a.seqr);
                4'h3: w_m_i.start(e.a.seqr);
                4'h4: w_m_d.start(e.a.seqr);
                4'h5: i_s.start(e.a.seqr);
            endcase
        end
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module memaccess_tb;
    memaccess_if vif();
    
    memaccess dut(
        .mem_state(vif.mem_state),
        .M_Control(vif.M_Control),
        .M_Data(vif.M_Data),
        .M_Addr(vif.M_Addr),  
        .DMem_dout(vif.DMem_dout),
        .DMem_addr(vif.DMem_addr),
        .DMem_rd(vif.DMem_rd),
        .DMem_din(vif.DMem_din),
        .memout(vif.memout)
    );

    initial begin
        uvm_config_db#(virtual memaccess_if)::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
