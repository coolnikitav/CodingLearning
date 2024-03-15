# Getting Started with Base Classes: UVM_OBJECT
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/14ff39ce-9e73-4002-b706-62ed6e3feff7)

Static components - components that remain live for the entire duration of the simulation: driver, monitor, scoreboard

On the other hand, there will be a unique transaction for each new piece of data - dynamic component.

In uvm, static components are built using UVM_COMPONENT (uvm_driver for driver) and dynamic ones are built using UVM_OBJECT (ex: uvm_sequence_item for transaction)

uvm_component itself is derived from uvm_object, so it has all of its properties. uvm_component has a uvm_tree and phases, unlike uvm_object. 

*Base Class*
- uvm_object
  - uvm_transaction
  - uvm_sequence_item
  - uvm_sequence
- uvm_component
  - uvm_driver
  - uvm_sequencer
  - uvm_monitor
  - uvm_agent
  - uvm_scoreboard
  - uvm_env
  - uvm_test
 
Core Methods (Field Macros of data members)
- Print
- Record
- Copy
- Compare
- Create
- Clone
- Pack + unpack

User defined do_methods
- do_print
- do_record
- do_copy
- do_compare
- do_pack
- do_unpack

When you specify implementation for any core method then Field Macros are not required.

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class obj extends uvm_object;  // object class is used to implement all dynamic components of testbench
  `uvm_object_utils(obj);  // macro to register class to factory derived from UVM_OBJECT
  
  function new(string path = "OBJ");
    super.new(path);
  endfunction
  
  rand bit [3:0] a;
  
endclass

module tb;
  
  obj o;
  
  initial begin
    o = new("obj");
    o.randomize();
    `uvm_info("TB_TOP", $sformatf("value of a: %0d", o.a), UVM_NONE);
  end
  
endmodule
```
