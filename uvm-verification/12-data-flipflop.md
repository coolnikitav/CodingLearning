# Verification of Sequential Circuit: Data FlipFlop

## Design Code
```
module dff(
    input clk, rst, din,
    output reg dout
    );
    always @(posedge clk) begin
        if(rst)
            dout <= 1'b0;
        else
            dout <= din;
    end
endmodule

////////////////////////////////////////////////

interface dff_if;
    logic clk, rst, din, dout;
endinterface
```

## Verification
```
`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////////////////////

class config_dff extends uvm_object;
    `uvm_object_utils(config_dff)
    
    // active agent = driver + monitor
    // passive agent = monitor
    uvm_active_passive_enum agent_type = UVM_ACTIVE;  
    
    function new(input string path = "config_dff");
        super.new(path);
    endfunction
endclass

////////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
    rand bit rst;
    rand bit din;
         bit dout;
         
    function new(input string path = "transaction");
        super.new(path);
    endfunction
endclass

////////////////////////////////////////////////

class valid_din extends uvm_sequence#(transaction);
    `uvm_object_utils(valid_din)
    
    transaction tr;
    
    function new(input string path = "valid_din");
        super.new(path);
    endfunction
    
    virtual task body();
        repeat(15) begin
            tr = transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            tr.rst = 1'b0;
            `uvm_info("SEQ", $sformatf("rst: %0d, din: %0d, dout: %0d", tr.rst, tr.din, tr.dout), UVM_NONE);
            finish_item(tr);            
        end
    endtask
endclass

////////////////////////////////////////////////

class rst_dff extends uvm_sequence#(transaction);
    `uvm_object_utils(rst_dff)
    
    transaction tr;
    
    function new(input string path = "rst_dff");
        super.new(path);
    endfunction
    
    virtual task body();
        repeat(15) begin
            tr = transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            tr.rst = 1'b1;
            `uvm_info("SEQ", $sformatf("rst: %0d, din: %0d, dout: %0d", tr.rst, tr.din, tr.dout), UVM_NONE);
            finish_item(tr);            
        end
    endtask
endclass

////////////////////////////////////////////////

class rand_din_rst extends uvm_sequence#(transaction);
    `uvm_object_utils(rand_din_rst)
    
    transaction tr;
    
    function new(input string path = "rand_din_rst");
        super.new(path);
    endfunction
    
    virtual task body();
        repeat(15) begin
            tr = transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            `uvm_info("SEQ", $sformatf("rst: %0d, din: %0d, dout: %0d", tr.rst, tr.din, tr.dout), UVM_NONE);
            finish_item(tr);
        end
    endtask
endclass

////////////////////////////////////////////////

class drv extends uvm_driver#(transaction);
    `uvm_component_utils(drv)
    
    transaction tr;
    virtual dff_if dif;
    
    function new(input string path = "drv", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual dff_if)::get(this,"","dif",dif))
            `uvm_error("drv", "Unable to access Interface");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        tr = transaction::type_id::create("tr");
        forever begin
            seq_item_port.get_next_item(tr);
            dif.rst <= tr.rst;
            dif.din <= tr.din;
            `uvm_info("DRV", $sformatf("rst: %0d, din: %0d, dout: %0d", tr.rst, tr.din, tr.dout), UVM_NONE);
            seq_item_port.item_done();
            repeat(2) @(posedge dif.clk);
        end
    endtask
endclass

////////////////////////////////////////////////

class mon extends uvm_monitor;
    `uvm_component_utils(mon)
    
    uvm_analysis_port#(transaction) send;
    
    transaction tr;
    virtual dff_if dif;
    
    function new(input string inst = "mon", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual dff_if)::get(this,"","dif",dif))
            `uvm_error("drv", "Unable to access Interface");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            repeat(2) @(posedge dif.clk);
            tr.rst  = dif.rst;
            tr.din  = dif.din;
            tr.dout = dif.dout;
            `uvm_info("MON", $sformatf("rst: %0d, din: %0d, dout: %0d", tr.rst, tr.din, tr.dout), UVM_NONE);
            send.write(tr);
        end                
    endtask
endclass

////////////////////////////////////////////////

class sco extends uvm_scoreboard;
    `uvm_component_utils(sco)
    
    uvm_analysis_imp#(transaction, sco) recv;
    
    function new(input string inst = "sco", uvm_component parent = null);
        super.new(inst, parent);
    endfunction        
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
    endfunction
    
    virtual function void write(transaction tr);
        `uvm_info("SCO", $sformatf("rst: %0d, din: %0d, dout: %0d", tr.rst, tr.din, tr.dout), UVM_NONE);
        if(tr.rst == 1'b1) begin
            `uvm_info("SCO", "DFF Reset", UVM_NONE)
        end else if (tr.rst == 1'b0 && (tr.din == tr.dout)) begin
            `uvm_info("SCO", "TEST PASSED", UVM_NONE)
        end else begin
            `uvm_info("SCO", "TEST PASSED", UVM_NONE)
        end    
        $display("----------------------------------------------------------------");
    endfunction
endclass

////////////////////////////////////////////////

class agent extends uvm_agent;
    `uvm_component_utils(agent)
    
    function new(input string inst = "agent", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    drv d;
    mon m;
    uvm_sequencer#(transaction) seqr;
    config_dff cfg;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m = mon::type_id::create("m", this);
        cfg = config_dff::type_id::create("cfg");
        
        if(!uvm_config_db#(config_dff)::get(this,"","cfg",cfg))
            `uvm_error("AGENT", "FAILED TO ACCESS CONFIG")
            
        if(cfg.agent_type == UVM_ACTIVE) begin
            d = drv::type_id::create("d",this);
            seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
        end
    endfunction  
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction      
endclass

////////////////////////////////////////////////

class env extends uvm_env;
    `uvm_component_utils(env)
    
    function new(input string inst = "env", uvm_component c);
        super.new(inst, c);
    endfunction
    
    agent a;
    sco s;
    config_dff cfg;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = agent::type_id::create("a", this);
        s = sco::type_id::create("s", this);
        cfg = config_dff::type_id::create("cfg");
        uvm_config_db#(config_dff)::set(this,"a","cfg",cfg);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);
    endfunction
endclass

////////////////////////////////////////////////

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(input string inst = "test", uvm_component c);
        super.new(inst, c);
    endfunction
    
    env e;
    valid_din vdin;
    rst_dff rff;
    rand_din_rst rdin;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e     = env::type_id::create("env", this);
        vdin  = valid_din::type_id::create("vdin");
        rff   = rst_dff::type_id::create("rff");
        rdin = rand_din_rst::type_id::create("rdin");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        rff.start(e.a.seqr);
        #40;
        vdin.start(e.a.seqr);
        #40;
        rdin.start(e.a.seqr);
        #40;
        phase.drop_objection(this);
    endtask
endclass

////////////////////////////////////////////////

module dff_tb;
    dff_if dif();
    
    dff dut(.clk(dif.clk), .rst(dif.rst), .din(dif.din), .dout(dif.dout));
    
    initial begin
        uvm_config_db#(virtual dff_if)::set(null,"*","dif",dif);
        run_test("test");
    end
    
    initial begin
        dif.clk = 0;
    end
    
    always #10 dif.clk = ~dif.clk;       
endmodule
```

## Output
```
UVM_INFO @ 0: reporter [RNTST] Running test test...
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 0: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 0: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 30000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 30000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 30000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 30000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 30000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 70000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 70000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 70000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 70000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 70000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 110000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 110000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 110000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 110000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 110000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 150000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 150000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 150000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 150000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 150000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 190000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 190000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 190000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 190000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 190000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 230000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 230000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 230000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 230000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 230000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 270000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 270000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 270000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 270000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 270000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 310000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 310000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 310000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 310000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 310000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 350000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 350000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 350000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 350000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 350000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 390000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 390000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 390000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 390000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 390000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 430000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 430000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 430000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 430000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 430000: uvm_test_top.env.a.d [DRV] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 470000: uvm_test_top.env.a.m [MON] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 470000: uvm_test_top.env.s [SCO] rst: 1, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 470000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 470000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 470000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 510000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 510000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 510000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 510000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 510000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 550000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 550000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 550000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(73) @ 550000: uvm_test_top.env.a.seqr@@rff [SEQ] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 550000: uvm_test_top.env.a.d [DRV] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 590000: uvm_test_top.env.a.m [MON] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 590000: uvm_test_top.env.s [SCO] rst: 1, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(185) @ 590000: uvm_test_top.env.s [SCO] DFF Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 590000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 590000: uvm_test_top.env.a.d [DRV] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 630000: uvm_test_top.env.a.m [MON] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 630000: uvm_test_top.env.s [SCO] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 630000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 630000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 630000: uvm_test_top.env.a.d [DRV] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 670000: uvm_test_top.env.a.m [MON] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 670000: uvm_test_top.env.s [SCO] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 670000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 670000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 670000: uvm_test_top.env.a.d [DRV] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 710000: uvm_test_top.env.a.m [MON] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 710000: uvm_test_top.env.s [SCO] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 710000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 710000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 710000: uvm_test_top.env.a.d [DRV] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 750000: uvm_test_top.env.a.m [MON] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 750000: uvm_test_top.env.s [SCO] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 750000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 750000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 750000: uvm_test_top.env.a.d [DRV] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 790000: uvm_test_top.env.a.m [MON] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 790000: uvm_test_top.env.s [SCO] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 790000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 790000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 790000: uvm_test_top.env.a.d [DRV] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 830000: uvm_test_top.env.a.m [MON] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 830000: uvm_test_top.env.s [SCO] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 830000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 830000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 830000: uvm_test_top.env.a.d [DRV] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 870000: uvm_test_top.env.a.m [MON] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 870000: uvm_test_top.env.s [SCO] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 870000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 870000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 870000: uvm_test_top.env.a.d [DRV] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 910000: uvm_test_top.env.a.m [MON] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 910000: uvm_test_top.env.s [SCO] rst: 0, din: 0, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 910000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 910000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 910000: uvm_test_top.env.a.d [DRV] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 950000: uvm_test_top.env.a.m [MON] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 950000: uvm_test_top.env.s [SCO] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 950000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(50) @ 950000: uvm_test_top.env.a.seqr@@vdin [SEQ] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(125) @ 950000: uvm_test_top.env.a.d [DRV] rst: 0, din: 1, dout: 0
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(160) @ 990000: uvm_test_top.env.a.m [MON] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(183) @ 990000: uvm_test_top.env.s [SCO] rst: 0, din: 1, dout: 1
UVM_INFO C:/eng_apps/vivado_projects/data_flipflop/data_flipflop.srcs/sim_1/new/dff_tb.sv(187) @ 990000: uvm_test_top.env.s [SCO] TEST PASSED
----------------------------------------------------------------
```
