# UVM_COMPONENT
## Understanding UVM_TREE
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1e4b1414-26f9-4e9c-9f7d-12119d73da7b)

uvm_test -> child, uvm_top -> parent

## Creating UVM_COMPONENT class
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class comp extends uvm_component;
  `uvm_component_utils(comp)  // register to a factory
  
  function new (string path = "comp", uvm_component parent = null);
    super.new(path,parent);
  endfunction
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("COMP", "Build phase of comp executed", UVM_NONE)
  endfunction
endclass

module tb;
  initial begin
    run_test("comp");  // execute code of com class
  end
endmodule

# KERNEL: UVM_INFO @ 0: reporter [RNTST] Running test comp...
# KERNEL: UVM_INFO /home/runner/testbench.sv(13) @ 0: uvm_test_top [COMP] Build phase of comp executed
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 0: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    3
# KERNEL: UVM_WARNING :    0
# KERNEL: UVM_ERROR :    0
# KERNEL: UVM_FATAL :    0
# KERNEL: ** Report counts by id
# KERNEL: [COMP]     1
# KERNEL: [RNTST]     1
# KERNEL: [UVM/RELNOTES]     1
# KERNEL: 
# RUNTIME: Info: RUNTIME_0068 uvm_root.svh (521): $finish called.
```

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class comp extends uvm_component;
  `uvm_component_utils(comp)  // register to a factory
  
  function new (string path = "comp", uvm_component parent = null);
    super.new(path,parent);
  endfunction
  
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("COMP", "Build phase of comp executed", UVM_NONE)
  endfunction
endclass

module tb;
  comp c;
  
  initial begin
    c = comp::type_id::create("c", null);
    c.build_phase(null);
  end
  
  /*
  initial begin
    run_test("comp");  // execute code of com class
  end*/
endmodule

# KERNEL: UVM_WARNING @ 0: c [UVM_DEPRECATED] build()/build_phase() has been called explicitly, outside of the phasing system. This usage of build is deprecated and may lead to unexpected behavior.
# KERNEL: UVM_INFO /home/runner/testbench.sv(13) @ 0: c [COMP] Build phase of comp executed
```

## Creating UVM_TREE P1
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1b5ff5ce-c5cc-49b6-a07e-fb21547445ab)
```
`include "uvm_macros.svh";
import uvm_pkg::*;

class a extends uvm_component;
  `uvm_component_utils(a)
  
  function new(string path = "a", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("a", "Class a executed", UVM_NONE);
  endfunction
endclass

//////////////////////////////

class b extends uvm_component;
  `uvm_component_utils(b)
  
  function new(string path = "b", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("b", "Class b executed", UVM_NONE);
  endfunction
endclass

//////////////////////////////

class c extends uvm_component;
  `uvm_component_utils(c)
  
  a a_inst;
  b b_inst;
  
  function new(string path = "c", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    a_inst = a::type_id::create("a_inst", this);  // "this" refers to class c
    b_inst = b::type_id::create("b_inst", this);
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_top.print_topology();
  endfunction
endclass

//////////////////////////////

module tb;
  initial begin
    run_test("c");
  end
endmodule

# KERNEL: UVM_INFO @ 0: reporter [RNTST] Running test c...
# KERNEL: UVM_INFO /home/runner/testbench.sv(13) @ 0: uvm_test_top.a_inst [a] Class a executed
# KERNEL: UVM_INFO /home/runner/testbench.sv(28) @ 0: uvm_test_top.b_inst [b] Class b executed
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_root.svh(583) @ 0: reporter [UVMTOP] UVM testbench topology:
# KERNEL: -------------------------------
# KERNEL: Name          Type  Size  Value
# KERNEL: -------------------------------
# KERNEL: uvm_test_top  c     -     @335 
# KERNEL:   a_inst      a     -     @348 
# KERNEL:   b_inst      b     -     @357 
# KERNEL: -------------------------------
# KERNEL: 
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 0: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    5
# KERNEL: UVM_WARNING :    0
# KERNEL: UVM_ERROR :    0
# KERNEL: UVM_FATAL :    0
# KERNEL: ** Report counts by id
# KERNEL: [RNTST]     1
# KERNEL: [UVM/RELNOTES]     1
# KERNEL: [UVMTOP]     1
# KERNEL: [a]     1
# KERNEL: [b]     1
# RUNTIME: Info: RUNTIME_0068 uvm_root.svh (521): $finish called.
```

## Creating UVM_TREE P2
Manual way of doing this, not recommended:
```
`include "uvm_macros.svh";
import uvm_pkg::*;

class a extends uvm_component;
  `uvm_component_utils(a)
  
  function new(string path = "a", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("a", "Class a executed", UVM_NONE);
  endfunction
endclass

//////////////////////////////

class b extends uvm_component;
  `uvm_component_utils(b)
  
  function new(string path = "b", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("b", "Class b executed", UVM_NONE);
  endfunction
endclass

//////////////////////////////

class c extends uvm_component;
  `uvm_component_utils(c)
  
  a a_inst;
  b b_inst;
  
  function new(string path = "c", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    a_inst = a::type_id::create("a_inst", this);  // "this" refers to class c
    b_inst = b::type_id::create("b_inst", this);
    a_inst.build_phase(null);
    b_inst.build_phase(null);
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_top.print_topology();
  endfunction
endclass

//////////////////////////////

module tb;
  // not recommended
  c c_inst;
  
  initial begin
    c_inst = c::type_id::create("c_inst", null);
    c_inst.build_phase(null);
  end
endmodule

# KERNEL: UVM_WARNING @ 0: c_inst [UVM_DEPRECATED] build()/build_phase() has been called explicitly, outside of the phasing system. This usage of build is deprecated and may lead to unexpected behavior.
# KERNEL: UVM_WARNING @ 0: c_inst.a_inst [UVM_DEPRECATED] build()/build_phase() has been called explicitly, outside of the phasing system. This usage of build is deprecated and may lead to unexpected behavior.
# KERNEL: UVM_INFO /home/runner/testbench.sv(13) @ 0: c_inst.a_inst [a] Class a executed
# KERNEL: UVM_WARNING @ 0: c_inst.b_inst [UVM_DEPRECATED] build()/build_phase() has been called explicitly, outside of the phasing system. This usage of build is deprecated and may lead to unexpected behavior.
# KERNEL: UVM_INFO /home/runner/testbench.sv(28) @ 0: c_inst.b_inst [b] Class b executed
```
