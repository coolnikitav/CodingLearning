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

