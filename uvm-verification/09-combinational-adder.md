# Combinational Adder

## Summary of the Verification Environment
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f92bbe5c-e194-4498-80aa-a812a046d78c)

- Driver will request for a sequence and the sequencer will send it.
- Monitor will forward DUT output to the scoreboard with the help of UVM_ANALYSIS_PORT

Classes:
- Transaction: keep track of all the I/O present in DUT (uvm_sequence_item)
- Sequence: combination of transactions to verify specific test case (uvm_sequence)
- Sequencer: manage sequences. Send sequence to driver after request(uvm_sequencer)
- Driver: send request to driver for sequence, apply sequence to the DUT (uvm_driver)
- Monitor: collect response fo DUT and forward to scoreboard (uvm_monitor)
- Scoreboard: compare response with golden data (uvm_scoreboard)
- Agent: Encapsulate Driver, Sequence, Monitor. Connection of driver and sequencer TLM port (uvm_agent)
- Env: Encapsulate Agent and Scoreboard. Connection of analysis port of MON, SCO (uvm_env)
- Test: Encapsulate Env. start sequence (uvm_test)

## Verification of Combinational Adder: DUT
```
`timescale 1ns / 1ps

module add(
    input  [3:0] a, b,
    output [4:0] y
    );
    assign y = a + b;    
endmodule

interface add_if();
    logic [3:0] a,b;
    logic [4:0] y;
endinterface
```

## Testbench
```
`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    rand bit [3:0] a;
    rand bit [3:0] b;
         bit [4:0] y;
         
    function new(input string path = "transaction");
        super.new(path);
    endfunction
    
    `uvm_object_utils_begin(transaction)
        `uvm_field_int(a, UVM_DEFAULT);
        `uvm_field_int(b, UVM_DEFAULT);
        `uvm_field_int(y, UVM_DEFAULT);
    `uvm_object_utils_end
endclass

///////////////////////////////////////////////////

class generator extends uvm_sequence#(transaction);
    `uvm_object_utils(generator)
    
    transaction t;
    
    function new(input string path = "generator");
        super.new(path);
    endfunction
    
    virtual task body();
        t = transaction::type_id::create("t");
        repeat(10) begin
            start_item(t);
            t.randomize();
            `uvm_info("GEN", $sformatf("Data sent to Driver: a = %0d, b = %0d", t.a, t.b), UVM_NONE);
            finish_item(t);
        end
    endtask
endclass

///////////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    transaction tc;
    virtual add_if aif;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tc = transaction::type_id::create("tc");
        
        if(!uvm_config_db#(virtual add_if)::get(this,"","aif",aif))
            `uvm_error("DRV", "Unable to access uvm_config_db");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(tc);
            aif.a <= tc.a;
            aif.b <= tc.b;
            `uvm_info("DRV", $sformatf("Trigger DUT a: %0d, b: %0d", tc.a, tc.b), UVM_NONE);
            seq_item_port.item_done();
            #10;
        end
    endtask
endclass

///////////////////////////////////////////////////

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) send;
    
    transaction t;
    virtual add_if aif;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
        send = new("send", this);       
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        t = transaction::type_id::create("TRANS");
        
        if(!uvm_config_db#(virtual add_if)::get(this,"","aif",aif))
            `uvm_error("MON", "Unable to access uvm_config_db");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            #10;
            t.a = aif.a;
            t.b = aif.b;
            t.y = aif.y;
            `uvm_info("MON", $sformatf("Data sent to scoreboard a: %0d, b: %0d, y: %0d", t.a, t.b, t.y), UVM_NONE);
            send.write(t);
        end
    endtask
endclass

///////////////////////////////////////////////////

class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(scoreboard)
    
    uvm_analysis_imp#(transaction, scoreboard) recv;
    
    transaction tr;
    
    function new(input string path = "scoreboard", uvm_component parent = null);
        super.new(path, parent);
        recv = new("recv", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
    endfunction
    
    virtual function void write(input transaction t);
        tr = t;
        `uvm_info("SCO", $sformatf("Data rcvd from Monitor a: %0d, b: %0d and y: %0d", tr.a, tr.b, tr.y), UVM_NONE);
        
        if(tr.y == tr.a + tr.b) begin
            `uvm_info("SCO", "Test Passed", UVM_NONE);
        end else begin
            `uvm_info("SCO", "Test Failed", UVM_NONE);
        end
    endfunction
endclass
///////////////////////////////////////////////////

class agent extends uvm_agent;
    `uvm_component_utils(agent)
    
    monitor m;
    driver d;
    uvm_sequencer#(transaction) seqr;
    
    function new(input string inst = "AGENT", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m    = monitor::type_id::create("m", this);
        d    = driver::type_id::create("d", this);
        seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass
///////////////////////////////////////////////////

class env extends uvm_env;
    `uvm_component_utils(env)
    
    scoreboard s;
    agent a;
    
    function new(input string inst = "ENV", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        s = scoreboard::type_id::create("s", this);
        a = agent::type_id::create("a", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);
    endfunction
endclass

///////////////////////////////////////////////////

class test extends uvm_test;
    `uvm_component_utils(test)
    
    generator gen;
    env e;
    
    function new(input string inst = "TEST", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        gen = generator::type_id::create("gen");
        e = env::type_id::create("e", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        gen.start(e.a.seqr);
        #50;  // give time for all tests to complete
        phase.drop_objection(this);        
    endtask
endclass

///////////////////////////////////////////////////

module add_tb;
    add_if aif();
    
    add dut (.a(aif.a), .b(aif.b), .y(aif.y));
    
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
    
    initial begin
        uvm_config_db#(virtual add_if)::set(null, "uvm_test_top.e.a*", "aif", aif);
        run_test("test");
    end
endmodule

UVM_INFO @ 0: reporter [RNTST] Running test test...
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 0: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 15, b = 5
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 0: uvm_test_top.e.a.d [DRV] Trigger DUT a: 15, b: 5
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 10000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 15, b: 5, y: 20
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 10000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 15, b: 5 and y: 20
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 10000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 10000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 3, b = 5
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 10000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 3, b: 5
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 20000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 3, b: 5, y: 8
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 20000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 3, b: 5 and y: 8
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 20000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 20000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 5, b = 14
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 20000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 5, b: 14
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 30000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 5, b: 14, y: 19
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 30000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 5, b: 14 and y: 19
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 30000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 30000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 1, b = 0
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 30000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 1, b: 0
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 40000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 1, b: 0, y: 1
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 40000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 1, b: 0 and y: 1
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 40000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 40000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 4, b = 3
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 40000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 4, b: 3
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 50000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 4, b: 3, y: 7
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 50000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 4, b: 3 and y: 7
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 50000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 50000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 0, b = 2
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 50000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 0, b: 2
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 60000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 0, b: 2, y: 2
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 60000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 0, b: 2 and y: 2
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 60000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 60000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 14, b = 3
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 60000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 14, b: 3
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 70000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 14, b: 3, y: 17
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 70000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 14, b: 3 and y: 17
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 70000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 70000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 7, b = 3
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 70000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 7, b: 3
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 80000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 7, b: 3, y: 10
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 80000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 7, b: 3 and y: 10
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 80000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 80000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 9, b = 11
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 80000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 9, b: 11
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 90000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 9, b: 11, y: 20
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 90000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 9, b: 11 and y: 20
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 90000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(40) @ 90000: uvm_test_top.e.a.seqr@@gen [GEN] Data sent to Driver: a = 6, b = 15
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(71) @ 90000: uvm_test_top.e.a.d [DRV] Trigger DUT a: 6, b: 15
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 100000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 6, b: 15, y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 100000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 6, b: 15 and y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 100000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 110000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 6, b: 15, y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 110000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 6, b: 15 and y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 110000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 120000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 6, b: 15, y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 120000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 6, b: 15 and y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 120000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 130000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 6, b: 15, y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 130000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 6, b: 15 and y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 130000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(107) @ 140000: uvm_test_top.e.a.m [MON] Data sent to scoreboard a: 6, b: 15, y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(134) @ 140000: uvm_test_top.e.s [SCO] Data rcvd from Monitor a: 6, b: 15 and y: 21
UVM_INFO C:/eng_apps/vivado_projects/09_Combinational_Adder/09_Combinational_Adder.srcs/sim_1/new/add_tb.sv(137) @ 140000: uvm_test_top.e.s [SCO] Test Passed
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(19968) @ 140000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(13673) @ 140000: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---
```
