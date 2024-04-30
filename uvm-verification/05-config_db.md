# config_db

## Understanding typical format of config_db
- Q: What does the set method look like? What does it do? What are its parameters?
- Q: What does the get method look like? What does it do? What are its parameters?

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class env extends uvm_env;
  `uvm_component_utils(env)
  
  int data;
  
  function new (string path = "env", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    
    if (uvm_config_db#(int)::get(null, "uvm_test_top", "data", data))
      `uvm_info("ENV", $sformatf("value of data : %0d", data), UVM_NONE)
    else
      `uvm_error("ENV", "Unable to accdess the value");
  endfunction
  
endclass

////////////////////////////

class test extends uvm_test;
  `uvm_component_utils(test)
  
  env e;
  
  function new (string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("e", this);
    
    /* 
     * parameters:
     *   context - null refers to UVM_ROOT, thus every component in tb would have access to the value
     *	 instance name
     *   key
     *   value
     */
    uvm_config_db#(int)::set(null, "uvm_test_top", "data", 12);
  endfunction
  
endclass

////////////////////////////

module tb;
  initial begin
    run_test("test");
  end
endmodule

# KERNEL: UVM_INFO @ 0: reporter [RNTST] Running test test...
# KERNEL: UVM_INFO /home/runner/testbench.sv(17) @ 0: uvm_test_top.e [ENV] value of data : 12
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 0: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    3
# KERNEL: UVM_WARNING :    0
# KERNEL: UVM_ERROR :    0
# KERNEL: UVM_FATAL :    0
# KERNEL: ** Report counts by id
# KERNEL: [ENV]     1
# KERNEL: [RNTST]     1
# KERNEL: [UVM/RELNOTES]     1
```

## Demonstration
uvm_config_db:
- set: set the value of a parameter that we will share between classes
- get: retrieve value of parameter that is set by set method

set parameters:
- #(int) - type of parameter that is being passed. Usually we pass virtual interfaces
- context - common value for static components is null and common value for dynamic components is this
- instance name - string, usually the name of the class that we provide
- key - name of the variable which value we are sharing
- value - value of the data

get parameters:
- #(int) - type of parameter that is being passed. Usually we pass virtual interfaces
- context - common value for static components is null and common value for dynamic components is this
- instance name - string, usually the name of the class that we provide
- key - name of the variable which value we are sharing
- data container - the variable we are passing

return true if operation is successful

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class comp1 extends uvm_component;
  `uvm_component_utils(comp1)
  
  int data1 = 0;
  
  function new (input string path = "comp1", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  // retrieve data sent by testbench top
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(null, "uvm_test_top", "data", data1))  // uvm_test_top.env.agent.comp1.data
      `uvm_error("comp1", "Unable to access Interface");
  endfunction
  
  // print value of data1
  virtual task run_phase (uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("comp1", $sformatf("Data rcvd comp1 : %0d", data1), UVM_NONE);
    phase.drop_objecion(this);
  endtask
endclass

////////////////////////////////

class comp2 extends uvm_component;
  `uvm_component_utils(comp2)
  
  int data2 = 0;
  
  function new (input string path = "comp2", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  // retrieve data sent by testbench top
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(int)::get(null, "uvm_test_top", "data", data2))  // uvm_test_top.env.agent.comp2.data
      `uvm_error("comp2", "Unable to access Interface");
  endfunction
  
  // print value of data1
  virtual task run_phase (uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("comp2", $sformatf("Data rcved comp2 : %0d", data2), UVM_NONE);
    phase.drop_objecion(this);
  endtask
endclass

////////////////////////////////

class agent extends uvm_agent;
  `uvm_component_utils(agent)
  
  function new (input string inst = "AGENT", uvm_component c);
    super.new(inst, c);
  endfunction
  
  comp1 c1;
  comp2 c2;
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    c1 = comp1::type_id::create("comp1", this);
    c2 = comp2::type_id::create("comp2", this);
  endfunction
endclass

////////////////////////////////

class env extends uvm_env;
  `uvm_component_utils(env)
  
  function new (input string inst = "ENV", uvm_component c);
    super.new(inst, c);
  endfunction
  
  agent a;
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    a = agent::type_id::create("AGENT", this);
  endfunction  
endclass

////////////////////////////////

class test extends uvm_test;
  `uvm_component_utils(test)
  
  function new (input string inst = "TEST", uvm_component c);
    super.new(inst, c);
  endfunction
  
  env e;
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("ENV", this);
  endfunction
endclass

////////////////////////////////

module tb;
  int data = 256;
  
  initial begin
    uvm_config_db#(int)::set(null, "uvm_test_top", "data", data);  // uvm_test_top.data
    run_test("test");
  end
endmodule
```

## Use Case
design.sv
```
module adder (
  input  [3:0] a,b,
  output [4:0] y
);
  assign y = a+b;
endmodule

interface adder_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] y;
endinterface
```

testbench.sv
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class drv extends uvm_driver;
  `uvm_component_utils(drv)
  
  virtual adder_if aif;
  
  function new (input string path = "drv", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual adder_if)::get(this, "", "aif", aif))  // uvm_test_top.env.agent.comp1.data
      `uvm_error("drv", "Unable to access Interface");
  endfunction
  
  virtual task run_phase (uvm_phase phase);
    phase.raise_objection(this);
    for (int i = 0; i < 10; i++) begin
      aif.a <= $urandom;
      aif.b <= $urandom;
      #10;
    end
    phase.drop_objection(this);
  endtask
endclass

////////////////////////////////////

class agent extends uvm_agent;
  `uvm_component_utils(agent)
  
  function new (input string inst = "agent", uvm_component c);
    super.new(inst, c);
  endfunction
  
  drv d;
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    d = drv::type_id::create("drv", this);
  endfunction
endclass

////////////////////////////////////

class env extends uvm_env;
  `uvm_component_utils(env)
  
  function new (input string inst = "env", uvm_component c);
    super.new(inst, c);
  endfunction
  
  agent a;
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    a = agent::type_id::create("agent", this);
  endfunction
endclass

////////////////////////////////////

class test extends uvm_test;
  `uvm_component_utils(test)
  
  function new (input string inst = "test", uvm_component c);
    super.new(inst, c);
  endfunction
  
  env e;
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("env", this);
  endfunction
endclass
                             
////////////////////////////////////
                             
module tb;
  adder_if aif();
  
  adder dut (.a(aif.a), .b(aif.b), .y(aif.y));
  
  initial begin
    uvm_config_db #(virtual adder_if)::set(null, "uvm_test_top.env.agent.drv", "aif", aif);
    run_test("test");
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule

# KERNEL: UVM_INFO @ 0: reporter [RNTST] Running test test...
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_objection.svh(1271) @ 100: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 100: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    3
# KERNEL: UVM_WARNING :    0
# KERNEL: UVM_ERROR :    0
# KERNEL: UVM_FATAL :    0
# KERNEL: ** Report counts by id
# KERNEL: [RNTST]     1
# KERNEL: [TEST_DONE]     1
# KERNEL: [UVM/RELNOTES]     1
```
