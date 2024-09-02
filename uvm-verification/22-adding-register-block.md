# Adding Register Block
![image](https://github.com/user-attachments/assets/0c2386c5-ab25-4181-b9f9-34d63a96d217)

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class reg1 extends uvm_reg;
  `uvm_object_utils(reg1)
  
  rand uvm_reg_field ctrl;
  
  function new(string name = "reg1");
    super.new(name,32,UVM_NO_COVERAGE);
  endfunction
  
  function void build;
    ctrl = uvm_reg_field::type_id::create("ctrl");
    ctrl.configure(
      .parent(this),
      .size(32),
      .lsb_pos(0),
      .access("RW"),
      .volatile(0),
      .reset(0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(1)
    );
  endfunction
endclass

class reg2 extends uvm_reg;
  `uvm_object_utils(reg2)
  
  rand uvm_reg_field data;
  
  function new(string name = "reg2");
    super.new(name,32,UVM_NO_COVERAGE);
  endfunction
  
  function void build;
    data = uvm_reg_field::type_id::create("data");
    data.configure(
      .parent(this),
      .size(32),
      .lsb_pos(0),
      .access("RW"),
      .volatile(0),
      .reset(0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(1)
    );
  endfunction
endclass

class top_reg_block extends uvm_reg_block;
  `uvm_object_utils(top_reg_block)
  
  rand reg1 reg1_inst;
  rand reg2 reg2_inst;
  
  function new(string name = "top_reg_block");
    super.new(name, UVM_NO_COVERAGE);
  endfunction
  
  function void build;
    reg1_inst = reg1::type_id::create("reg1_inst");
    reg1_inst.build();
    reg1_inst.configure(this);
    
    reg2_inst = reg2::type_id::create("reg2_inst");
    reg2_inst.build();
    reg2_inst.configure(this);
    
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
    default_map.add_reg(reg1_inst, 0, "RW");
    default_map.add_reg(reg2_inst, 4, "RW");
    
    lock_model();
  endfunction
endclass
```
