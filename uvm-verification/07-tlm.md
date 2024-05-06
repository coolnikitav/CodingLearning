# TLM (Transaction Level Modeling)

## Fundamentals
- Q1: What is a sequencer?
- Q2: What does TLM use instead of classes?
  
Sequencer is uvm's generator.

- Sequencer -> Driver : Special TLM Port : SEQ_ITEM_PORT
- Monitor -> Scoreboard : TLM Port : UVM_ANALYSIS PORT

TLM does not use classes. We use port(initiator) and export(responder)

- Put operation: Initiator A sends data to responder B.
- Get operation: Initiator A gets data from responder B.
- Transport operation: Data flows back and forth between A and B.

All of these operations can be implemented in a blocking or nonblocking manner.

## Blocking PUT Operation
- Q: What are the 3 functions? Write them out.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f3ba0f99-25c0-4da4-ae73-1039831d21ab)

- uvm_blocking_put_port #(parameter) // parameter is the type of data you are communicating
- uvm_blocking_put_export #(parameter)
- uvm_blocking_put_imp #(parameter)  // implementation

- Connection of TLM port operating between Driver and Sequencer happens in connect_phase of agent
- Connection of TLM port operating between Monitor and Scoreboard happens in connect_phase of environment
 
```
`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

class producer extends uvm_component;
    `uvm_component_utils(producer)
    
    int data = 12;
    
    uvm_blocking_put_port #(int) send;
    
    function new (input string path = "producer", uvm_component parent = null);
        super.new(path, parent);
        send = new("send", this);
    endfunction
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        send.put(data);
        `uvm_info("PROD", $sformatf("Data sent: %0d", data), UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

/////////////////////////////////////

class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    
    uvm_blocking_put_export #(int)           recv;
    uvm_blocking_put_imp    #(int, consumer) imp;
    
    function new (input string path = "consumer", uvm_component parent = null);
        super.new(path, parent);
        recv = new("recv", this);
        imp  = new("imp",  this);
    endfunction
    
    task put (int datar);
        `uvm_info("CONS", $sformatf("Data rcvd: %0d", datar), UVM_NONE);
    endtask
endclass

/////////////////////////////////////

class env extends uvm_component;
    `uvm_component_utils(env)
    
    producer p;
    consumer c;
    
    function new (input string path = "env", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        p = producer::type_id::create("p", this);
        c = consumer::type_id::create("c", this);
    endfunction
    
    virtual function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        p.send.connect(c.recv);  // connecting port and export
        c.recv.connect(c.imp);   // going from export to implementation
    endfunction
endclass

/////////////////////////////////////

class test extends uvm_component;
    `uvm_component_utils(test)
    
    env e;
    
    function new (input string path = "test", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
    endfunction
endclass

/////////////////////////////////////

module tlm;
    initial begin
        run_test("test");
    end
endmodule

UVM_INFO @ 0: reporter [RNTST] Running test test...
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/07_TLM/07_TLM.srcs/sim_1/new/tlm.sv(40) @ 0: uvm_test_top.e.c [CONS] Data rcvd: 12
UVM_INFO C:/eng_apps/vivado_projects/07_TLM/07_TLM.srcs/sim_1/new/tlm.sv(20) @ 0: uvm_test_top.e.p [PROD] Data sent: 12
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(13673) @ 0: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---

** Report counts by severity
UVM_INFO :    5
UVM_WARNING :    0
UVM_ERROR :    0
UVM_FATAL :    0
** Report counts by id
[CONS]     1
[PROD]     1
[RNTST]     1
[UVM/COMP/NAMECHECK]     1
[UVM/RELNOTES]     1
```

## Port to IMP
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2ea58f17-4560-4b22-8ea4-b1b2cdd9ea0c)

```
`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

class producer extends uvm_component;
    `uvm_component_utils(producer)
    
    int data = 12;
    
    uvm_blocking_put_port #(int) send;
    
    function new (input string path = "producer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        send = new("send", this);
    endfunction
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        send.put(data);
        `uvm_info("PROD", $sformatf("Data sent: %0d", data), UVM_NONE);
        phase.drop_objection(this);
    endtask
endclass

/////////////////////////////////////

class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    
    uvm_blocking_put_imp #(int, consumer) imp;
    
    function new (input string path = "consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    function void put (int datar);
        `uvm_info("CONS", $sformatf("Data rcvd: %0d", datar), UVM_NONE);
    endfunction
endclass

/////////////////////////////////////

class env extends uvm_component;
    `uvm_component_utils(env)
    
    producer p;
    consumer c;
    
    function new (input string inst = "env", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        p = producer::type_id::create("p", this);
        c = consumer::type_id::create("c", this);
    endfunction
    
    virtual function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        p.send.connect(c.imp);
    endfunction
endclass

/////////////////////////////////////

class test extends uvm_component;
    `uvm_component_utils(test)
    
    env e;
    
    function new (input string inst = "test", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
    endfunction
endclass

/////////////////////////////////////

module tlm;    
    initial begin
        run_test("test");
    end
endmodule

UVM_INFO @ 0: reporter [RNTST] Running test test...
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/07_TLM/07_TLM.srcs/sim_1/new/tlm.sv(46) @ 0: uvm_test_top.e.c [CONS] Data rcvd: 12
UVM_INFO C:/eng_apps/vivado_projects/07_TLM/07_TLM.srcs/sim_1/new/tlm.sv(24) @ 0: uvm_test_top.e.p [PROD] Data sent: 12
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(13673) @ 0: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---

** Report counts by severity
UVM_INFO :    5
UVM_WARNING :    0
UVM_ERROR :    0
UVM_FATAL :    0
** Report counts by id
[CONS]     1
[PROD]     1
[RNTST]     1
[UVM/COMP/NAMECHECK]     1
[UVM/RELNOTES]     1
```

## Port-Port to IMP
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ebc51a15-f20c-4ec1-a9db-e7b4bd1faf0d)

```
`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

class subproducer extends uvm_component;
    `uvm_component_utils(subproducer)
    
    int data = 12;
    
    uvm_blocking_put_port #(int) subport;
    
    function new (input string path = "subproducer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        subport = new("subport", this);
    endfunction
    
    task main_phase (uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("SUBPROD", $sformatf("Data sent : %0d", data), UVM_NONE);
        subport.put(data);
        phase.drop_objection(this);
    endtask
endclass

/////////////////////////////////////

class producer extends uvm_component;
    `uvm_component_utils(producer)
    
    subproducer s;
    
    uvm_blocking_put_port #(int) port;
    
    function new (input string path = "producer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        port = new("port", this);
        s = subproducer::type_id::create("s", this);
    endfunction
    
    virtual function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        s.subport.connect(port);
    endfunction
endclass

/////////////////////////////////////

class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    
    uvm_blocking_put_imp #(int, consumer) imp;
    
    function new (input string path = "consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    function void put (int datar);
        `uvm_info("CONS", $sformatf("Data rcvd: %0d", datar), UVM_NONE);
    endfunction
endclass

/////////////////////////////////////

class env extends uvm_component;
    `uvm_component_utils(env)
    
    producer p;
    consumer c;
    
    function new (input string inst = "env", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        p = producer::type_id::create("p", this);
        c = consumer::type_id::create("c", this);
    endfunction
    
    virtual function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c.imp);
    endfunction
endclass

/////////////////////////////////////

class test extends uvm_component;
    `uvm_component_utils(test)
    
    env e;
    
    function new (input string inst = "test", uvm_component c);
        super.new(inst, c);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
    endfunction
    
    virtual function void end_of_elaboration_phase (uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
endclass

/////////////////////////////////////

module tlm;    
    initial begin
        run_test("test");
    end
endmodule

UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(18752) @ 0: reporter [UVMTOP] UVM testbench topology:
---------------------------------------------------
Name             Type                   Size  Value
---------------------------------------------------
uvm_test_top     test                   -     @334 
  e              env                    -     @347 
    c            consumer               -     @365 
      imp        uvm_blocking_put_imp   -     @374 
    p            producer               -     @356 
      port       uvm_blocking_put_port  -     @384 
      s          subproducer            -     @394 
        subport  uvm_blocking_put_port  -     @403 
---------------------------------------------------

UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/07_TLM/07_TLM.srcs/sim_1/new/tlm.sv(23) @ 0: uvm_test_top.e.p.s [SUBPROD] Data sent : 12
UVM_INFO C:/eng_apps/vivado_projects/07_TLM/07_TLM.srcs/sim_1/new/tlm.sv(71) @ 0: uvm_test_top.e.c [CONS] Data rcvd: 12
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(13673) @ 0: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---

** Report counts by severity
UVM_INFO :    6
UVM_WARNING :    0
UVM_ERROR :    0
UVM_FATAL :    0
** Report counts by id
[CONS]     1
[RNTST]     1
[SUBPROD]     1
[UVM/COMP/NAMECHECK]     1
[UVM/RELNOTES]     1
[UVMTOP]     1
```

## Port to Export-IMP
- consumer connec phase: expo.connect(s.imp)
- environment connect phase: p.port.connect(c.expo)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/84ceba9b-1c59-47f1-add6-e61d8dfc6126)

```
`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

/////////////////////////////////////

class producer extends uvm_component;
    `uvm_component_utils(producer)
    
    int data = 12;
    
    uvm_blocking_put_port #(int) port;
    
    function new (input string path = "producer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        port = new("port", this);
    endfunction
    
    task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("PROD", $sformatf("Data sent : %0d", data), UVM_NONE);
        port.put(data);
        phase.drop_objection(this);
    endtask
endclass

/////////////////////////////////////

class subconsumer extends uvm_component;
    `uvm_component_utils(subconsumer)
    
    uvm_blocking_put_imp #(int, subconsumer) imp;
    
    function new(input string path = "subconsumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void buld_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
    endfunction
    
    function void put(int datar);
        `uvm_info("SUBCONS", $sformatf("Data rcvd : %0d", datar), UVM_NONE);
    endfunction
endclass

/////////////////////////////////////

class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    
    uvm_blocking_put_export #(int) expo;
    subconsumer s;
    
    function new (input string path = "consumer", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        expo = new("expo", this);
        s = subconsumer::type_id::create("s", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        expo.connect(s.imp);
    endfunction
endclass

/////////////////////////////////////

class env extends uvm_component;
    `uvm_component_utils(env)
    
    producer p;
    consumer c;
    
    function new (input string path = "env", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        p = producer::type_id::create("p", this);
        c = consumer::type_id::create("c", this);
    endfunction
    
    virtual function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        p.port.connect(c.expo);
    endfunction
endclass

/////////////////////////////////////

class test extends uvm_component;
    `uvm_component_utils(test)
    
    env e;
    
    function new (input string path = "test", uvm_component parent = null);
        super.new(path, parent);
    endfunction
    
    virtual function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        e = env::type_id::create("e", this);
    endfunction
    
    virtual function void end_of_elaboration_phase (uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
endclass

/////////////////////////////////////

module tlm;    
    initial begin
        run_test("test");
    end
endmodule
```

## Get Operation
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c5f53cf0-a639-4a26-a178-e060d3b02b76)
