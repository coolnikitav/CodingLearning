# Verification of Combinational Circuit: 4-bit Multiplier

## Design Code
```
module mul(
    input [3:0] a,b,
    output [7:0] y
    );
    assign y = a * b;    
endmodule

interface mul_if;
    logic [3:0] a, b;
    logic [7:0] y;
endinterface
```

## Verification Environment
```
`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [7:0] y;
         
    function new(input string path = "transaction");
        super.new(path);
    endfunction
endclass

////////////////////////////////////

class generator extends uvm_sequence#(transaction);
    `uvm_object_utils(generator)
    
    transaction tr;
    
    function new(input string path = "generator");
        super.new(path);
    endfunction
    
    virtual task body();
        repeat(10) begin
            tr = transaction::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize());
            `uvm_info("GEN", $sformatf("a: %0d, b: %0d, y: %0d", tr.a, tr.b, tr.y), UVM_NONE);
            finish_item(tr);
        end
    endtask
endclass

////////////////////////////////////

class drv extends uvm_driver#(transaction);
    `uvm_component_utils(drv)
    
    transaction tr;
    virtual mul_if vif;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual mul_if)::get(this,"","vif",vif))
            `uvm_info("DRV", "Unable to access interface", UVM_NONE);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        tr = transaction::type_id::create("tr");
        forever begin
            seq_item_port.get_next_item(tr);
            vif.a <= tr.a;
            vif.b <= tr.b;
            `uvm_info("DRV", $sformatf("a: %0d, b: %0d, y: %0d", tr.a, tr.b, tr.y), UVM_NONE);
            seq_item_port.item_done();
            #20;
        end
    endtask
endclass

////////////////////////////////////

class mon extends uvm_monitor;
    `uvm_component_utils(mon)
    
    uvm_analysis_port#(transaction) send;
    
    transaction tr;
    virtual mul_if vif;
    
    function new(input string inst = "mon", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual mul_if)::get(this,"","vif",vif))  //uvm_test_top.env.agent.drv.aif
            `uvm_error("MON", "Unable to access Interface");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            #20;
            tr.a = vif.a;
            tr.b = vif.b;
            tr.y = vif.y;
            `uvm_info("MON", $sformatf("a: %0d, b: %0d, y: %0d", tr.a, tr.b, tr.y), UVM_NONE);
            send.write(tr);
        end
    endtask
endclass

////////////////////////////////////

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
        if(tr.y == tr.a * tr.b) begin
            `uvm_info("SCO", "Test Passed", UVM_NONE);
        end else begin
            `uvm_info("SCO", "Test Failed", UVM_NONE);
        end
        $display("------------------------------------------------------------");
    endfunction
endclass

////////////////////////////////////

class agent extends uvm_agent;
    `uvm_component_utils(agent)
    
    drv d;
    mon m;
    uvm_sequencer#(transaction) seqr;
    
    function new(input string inst = "agent", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        d = drv::type_id::create("d", this);
        m = mon::type_id::create("m", this);
        seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

////////////////////////////////////

class env extends uvm_env;
    `uvm_component_utils(env)
    
    agent a;
    sco s;
    
    function new(input string inst = "env", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = agent::type_id::create("a", this);
        s = sco::type_id::create("s", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);
    endfunction
endclass

////////////////////////////////////

class test extends uvm_test;
    `uvm_component_utils(test)
    
    env e;
    generator gen;
    
    function new(input string inst = "test", uvm_component c);
        super.new(inst, c);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
        gen = generator::type_id::create("gen");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        gen.start(e.a.seqr);
        #20;
        phase.drop_objection(this);
    endtask
endclass

////////////////////////////////////

module mul_tb;
    mul_if vif();
    
    mul dut(.a(vif.a), .b(vif.b), .y(vif.y));
    
    initial begin
        uvm_config_db#(virtual mul_if)::set(null, "*", "vif", vif);
        run_test("test");
    end
endmodule
```

## Output
```
UVM_INFO @ 0: reporter [RNTST] Running test test...
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 0: uvm_test_top.e.a.seqr@@gen [GEN] a: 5, b: 8, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 0: uvm_test_top.e.a.d [DRV] a: 5, b: 8, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 20000: uvm_test_top.e.a.m [MON] a: 5, b: 8, y: 40
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 20000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 20000: uvm_test_top.e.a.seqr@@gen [GEN] a: 2, b: 1, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 20000: uvm_test_top.e.a.d [DRV] a: 2, b: 1, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 40000: uvm_test_top.e.a.m [MON] a: 2, b: 1, y: 2
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 40000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 40000: uvm_test_top.e.a.seqr@@gen [GEN] a: 6, b: 7, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 40000: uvm_test_top.e.a.d [DRV] a: 6, b: 7, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 60000: uvm_test_top.e.a.m [MON] a: 6, b: 7, y: 42
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 60000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 60000: uvm_test_top.e.a.seqr@@gen [GEN] a: 5, b: 7, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 60000: uvm_test_top.e.a.d [DRV] a: 5, b: 7, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 80000: uvm_test_top.e.a.m [MON] a: 5, b: 7, y: 35
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 80000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 80000: uvm_test_top.e.a.seqr@@gen [GEN] a: 5, b: 12, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 80000: uvm_test_top.e.a.d [DRV] a: 5, b: 12, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 100000: uvm_test_top.e.a.m [MON] a: 5, b: 12, y: 60
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 100000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 100000: uvm_test_top.e.a.seqr@@gen [GEN] a: 4, b: 9, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 100000: uvm_test_top.e.a.d [DRV] a: 4, b: 9, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 120000: uvm_test_top.e.a.m [MON] a: 4, b: 9, y: 36
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 120000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 120000: uvm_test_top.e.a.seqr@@gen [GEN] a: 5, b: 11, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 120000: uvm_test_top.e.a.d [DRV] a: 5, b: 11, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 140000: uvm_test_top.e.a.m [MON] a: 5, b: 11, y: 55
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 140000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 140000: uvm_test_top.e.a.seqr@@gen [GEN] a: 7, b: 12, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 140000: uvm_test_top.e.a.d [DRV] a: 7, b: 12, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 160000: uvm_test_top.e.a.m [MON] a: 7, b: 12, y: 84
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 160000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 160000: uvm_test_top.e.a.seqr@@gen [GEN] a: 4, b: 12, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 160000: uvm_test_top.e.a.d [DRV] a: 4, b: 12, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 180000: uvm_test_top.e.a.m [MON] a: 4, b: 12, y: 48
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 180000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(35) @ 180000: uvm_test_top.e.a.seqr@@gen [GEN] a: 8, b: 9, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(65) @ 180000: uvm_test_top.e.a.d [DRV] a: 8, b: 9, y: 0
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(100) @ 200000: uvm_test_top.e.a.m [MON] a: 8, b: 9, y: 72
UVM_INFO C:/eng_apps/vivado_projects/4_bit_mul/4_bit_mul.srcs/sim_1/new/mul_tb.sv(124) @ 200000: uvm_test_top.e.s [SCO] Test Passed
------------------------------------------------------------
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(19968) @ 200000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(13673) @ 200000: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---
```
