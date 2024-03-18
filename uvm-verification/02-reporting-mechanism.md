# Reporting Mechanism

## Different reporting macros
uvm_info(ID, MSG, redundancy_level) // which lcass, message itself, messages higher than redundancy level do not get sent to the console

defual redundancy level = 200 

```C
typedef enum
{
  UVM_NONE   = 0,
  UVM_LOW    = 100,
  UVM_MEDIUM = 200,
  UVM_HIGH   = 300,
  UVM_FULL   = 400,
  UVM_DEBUG  = 500
} uvm_verbosity;
```
Verbosity is only used with UVM_INFO:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3df53648-d22e-4466-a3c2-29afd83d006d)


Report severity:
```C
typedef enum bit [1:0]
{
  UVM_INFO,
  UVM_WARNING,
  UVM_ERROR,
  UVM_FATAL
} uvm_severity;
```

uvm_warning(ID,MSG);

uvm_error(ID,MSG);

uvm_fatal(ID,MSG);

## Working with reporting macros
```
`include "uvm_macros.svh"  // `uvm_info
import uvm_pkg::*;

module tb;
  initial begin
    #5;  // UVM_INFO will show the time of message
    `uvm_info("TB_TOP", "Hello World", UVM_LOW);
    $display("Hello World with Display");
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(7) @ 5: reporter [TB_TOP] Hello World
# KERNEL: Hello World with Display
```
## Printing values of variables without automation
```
`include "uvm_macros.svh"  // `uvm_info
import uvm_pkg::*;

module tb;
  int data = 56;
  
  initial begin
    `uvm_info("TB_TOP",$sformatf("value of variable: %0d",data),UVM_NONE);
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(8) @ 0: reporter [TB_TOP] value of variable: 56
```

## Working with verbosity level
UVM_ROOT is parent to all the classes that we add in UVM Testbench environment (UVM Tree).

Because UVM_ROOT returns a null pointer, we cannot directly access it. However, in a few situations, we may need to access or configure the default settings of UVM_ROOT.

In such a case, UVM provides a global variable UVM_TOP which is accessible to all classes of environment. UVM_TOP could be used whenever we need to work with the UVM root.

```
`include "uvm_macros.svh"
import uvm_pkg::*;

module tb;
  initial begin
    $display("Default Verbosity Level: %0d", uvm_top.get_report_verbosity_level);
    #10;
    `uvm_info("TB_TOP", "Medium", UVM_MEDIUM);
    `uvm_info("TB_TOP", "High", UVM_HIGH);
    `uvm_info("TB_TOP", "Low", UVM_LOW);
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(8) @ 10: reporter [TB_TOP] Medium
# KERNEL: UVM_INFO /home/runner/testbench.sv(10) @ 10: reporter [TB_TOP] Low
```

```
`include "uvm_macros.svh"
import uvm_pkg::*;

module tb;
  initial begin
    $display("Default Verbosity Level: %0d", uvm_top.get_report_verbosity_level);
    #10;
    uvm_top.set_report_verbosity_level(UVM_HIGH);
    `uvm_info("TB_TOP", "Medium", UVM_MEDIUM);
    `uvm_info("TB_TOP", "High", UVM_HIGH);
    `uvm_info("TB_TOP", "Low", UVM_LOW);
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(9) @ 10: reporter [TB_TOP] Medium
# KERNEL: UVM_INFO /home/runner/testbench.sv(10) @ 10: reporter [TB_TOP] High
# KERNEL: UVM_INFO /home/runner/testbench.sv(11) @ 10: reporter [TB_TOP] Low
```
