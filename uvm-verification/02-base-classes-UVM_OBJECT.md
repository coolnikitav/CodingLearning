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

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class obj extends uvm_object;  // object class is used to implement all dynamic components of testbench
  
  function new(string path = "OBJ");
    super.new(path);
  endfunction
  
  rand bit [3:0] a;
  
  `uvm_object_utils_begin(obj)
  `uvm_field_int(a, UVM_DEFAULT)
  `uvm_object_utils_end
  
endclass

module tb;
  
  obj o;
  
  initial begin
    o = new("obj");
    o.randomize();
    o.print();
  end
  
endmodule
```
```
# KERNEL: ---------------------------
# KERNEL: Name  Type      Size  Value
# KERNEL: ---------------------------
# KERNEL: obj   obj       -     @335 
# KERNEL:   a   integral  4     'h6  
# KERNEL: ---------------------------
```

Field macros are not as run-time efficient nor as flexible as direct implementations of the do_* methods

Examples:
- Automation: print
- do_ method: do_print
- User method: display

```
o.print(uvm_default_tree_printer);

# KERNEL: obj: (obj@335) {
# KERNEL:   a: 'h6 
# KERNEL: }
```
```
o.print(uvm_default_line_printer);

# KERNEL: obj: (obj@335) { a: 'h6  }
```
```
`uvm_field_int(a, UVM_DEFAULT | UVM_BIN)

# KERNEL: obj: (obj@335) { a: 'b110  } 
```

If you don't register the variable to a factory, its name and value will not be printed:
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class obj extends uvm_object;  // object class is used to implement all dynamic components of testbench
  
  `uvm_object_utils(obj)
  
  function new(string path = "OBJ");
    super.new(path);
  endfunction
  
  rand bit [3:0] a;
  
  /*
  `uvm_object_utils_begin(obj)
  	`uvm_field_int(a, UVM_DEFAULT | UVM_BIN)
  `uvm_object_utils_end
  */
endclass

module tb;
  
  obj o;
  
  initial begin
    o = new("obj");
    o.randomize();
    o.print(uvm_default_table_printer);
  end
  
endmodule

# KERNEL: -----------------------
# KERNEL: Name  Type  Size  Value
# KERNEL: -----------------------
# KERNEL: obj   obj   -     @335 
# KERNEL: -----------------------
```

Variable a has a UVM_NOPRINT flag
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class obj extends uvm_object;  // object class is used to implement all dynamic components of testbench
    
  function new(string path = "OBJ");
    super.new(path);
  endfunction
  
  rand bit [3:0] a;
  rand bit [7:0] b;
  
  `uvm_object_utils_begin(obj)
  	`uvm_field_int(a, UVM_NOPRINT | UVM_BIN)
  	`uvm_field_int(b, UVM_DEFAULT | UVM_BIN)
  `uvm_object_utils_end
  
endclass

module tb;
  
  obj o;
  
  initial begin
    o = new("obj");
    o.randomize();
    o.print(uvm_default_table_printer);
  end
  
endmodule

# KERNEL: --------------------------------
# KERNEL: Name  Type      Size  Value     
# KERNEL: --------------------------------
# KERNEL: obj   obj       -     @335      
# KERNEL:   b   integral  8     'b10100101
# KERNEL: --------------------------------
```

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class obj extends uvm_object;  // object class is used to implement all dynamic components of testbench
   
  typedef enum bit [1:0] {s0,s1,s2,s3} state_type;
  rand state_type state;
  
  real temp = 12.34;
  string str = "UVM";
  
  function new(string path = "OBJ");
    super.new(path);
  endfunction
  
  `uvm_object_utils_begin(obj)
  	`uvm_field_enum(state_type, state, UVM_DEFAULT)
  	`uvm_field_string(str, UVM_DEFAULT)
  	`uvm_field_real(temp, UVM_DEFAULT)
  `uvm_object_utils_end
  
endclass

module tb;
  
  obj o;
  
  initial begin
    o = new("obj");
    o.print(uvm_default_table_printer);
  end
  
endmodule

# KERNEL: ------------------------------------
# KERNEL: Name     Type        Size  Value    
# KERNEL: ------------------------------------
# KERNEL: obj      obj         -     @335     
# KERNEL:   state  state_type  2     s0       
# KERNEL:   str    string      3     UVM      
# KERNEL:   temp   real        64    12.340000
# KERNEL: ------------------------------------
```

```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////

class parent extends uvm_object;
  
  function new (string path = "parent");
    super.new(path);
  endfunction
  
  rand bit [3:0] data;
  
  `uvm_object_utils_begin(parent)
  	`uvm_field_int(data, UVM_DEFAULT)
  `uvm_object_utils_end
  
endclass

////////////////////////////

class child extends uvm_object;
  
  parent p;
  
  function new (string path = "child");
    super.new(path);
    p = new("parent");  // build_phase + create
  endfunction
  
  `uvm_object_utils_begin(child)
  	`uvm_field_object(p, UVM_DEFAULT)
  `uvm_object_utils_end
  
endclass

////////////////////////////

module tb;
  
  child c;
  
  initial begin
    c = new("child");
    c.p.randomize();
    c.print();
  end
  
endmodule

# KERNEL: -------------------------------
# KERNEL: Name      Type      Size  Value
# KERNEL: -------------------------------
# KERNEL: child     child     -     @335 
# KERNEL:   p       parent    -     @336 
# KERNEL:     data  integral  4     'h2  
# KERNEL: -------------------------------
```
```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////

class array extends uvm_object;
  
  int arr1[3] = {1,2,3};  // static array
  
  int arr2[];             // dynamic array
  
  int arr3[$];            // queue
  
  int arr4[int];          // associative array
  
  function new (string path = "array");
    super.new(path);
  endfunction
  
  `uvm_object_utils_begin(array)
    `uvm_field_sarray_int(arr1, UVM_DEFAULT)
    `uvm_field_array_int(arr2, UVM_DEFAULT)
    `uvm_field_queue_int(arr3, UVM_DEFAULT)
    `uvm_field_aa_int_int(arr4, UVM_DEFAULT)
  `uvm_object_utils_end
  
  task run();
    // Dynamic array value update
    arr2    = new[3];
    arr2[0] = 2;
    arr2[1] = 2;
    arr2[2] = 2;
    
    // Queue
    arr3.push_front(3);
    arr3.push_front(3);
    
    // Associative array
    arr4[1] = 4;
    arr4[2] = 4;
    arr4[3] = 4;
    arr4[4] = 4;
  endtask
  
endclass

////////////////////////////

module tb;
  
  array a;
  
  initial begin
    a = new("array");
    a.run();
    a.print();
  end
  
endmodule

# KERNEL: ----------------------------------
# KERNEL: array    array         -     @335 
# KERNEL:   arr1   sa(integral)  3     -    
# KERNEL:     [0]  integral      32    'h1  
# KERNEL:     [1]  integral      32    'h2  
# KERNEL:     [2]  integral      32    'h3  
# KERNEL:   arr2   da(integral)  3     -    
# KERNEL:     [0]  integral      32    'h2  
# KERNEL:     [1]  integral      32    'h2  
# KERNEL:     [2]  integral      32    'h2  
# KERNEL:   arr3   da(integral)  2     -    
# KERNEL:     [0]  integral      32    'h3  
# KERNEL:     [1]  integral      32    'h3  
# KERNEL:   arr4   aa(int,int)   4     -    
# KERNEL:     [1]  integral      32    'h4  
# KERNEL:     [2]  integral      32    'h4  
# KERNEL:     [3]  integral      32    'h4  
# KERNEL:     [4]  integral      32    'h4  
```
