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

## Working with verbosity level and ID
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path, parent);
  endfunction
  
  task run();
    `uvm_info("DRV1", "Executed Driver1 Code", UVM_HIGH);
    `uvm_info("DRV2", "Executed Driver2 Code", UVM_HIGH);
  endtask
endclass

module tb;
  driver drv;
  
  initial begin
    drv = new("DRV", null);
    
    drv.set_report_id_verbosity("DRV1", UVM_HIGH);
    drv.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(12) @ 0: DRV [DRV1] Executed Driver1 Code
```

## Working with individual component
```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path, parent);
  endfunction
  
  task run();
    `uvm_info("DRV1", "Executed Driver1 Code", UVM_HIGH);
    `uvm_info("DRV2", "Executed Driver2 Code", UVM_HIGH);
  endtask
endclass

////////////////////////////////

class env extends uvm_env;
  `uvm_component_utils(env)
  
  function new (string path, uvm_component parent);
    super.new(path, parent);
  endfunction
  
  task run();
    `uvm_info("ENV1", "Executed ENV1 Code", UVM_HIGH);
    `uvm_info("ENV2", "Executed ENV2 Code", UVM_HIGH);
  endtask
endclass

////////////////////////////////
module tb;
  driver drv;
  env e;
  
  initial begin
    drv = new("DRV", null);
    e = new("ENV", null);
    
    e.set_report_verbosity_level(UVM_HIGH);
	drv.set_report_id_verbosity("DRV1", UVM_HIGH);
    
    drv.run();
    e.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(14) @ 0: DRV [DRV1] Executed Driver1 Code
# KERNEL: UVM_INFO /home/runner/testbench.sv(29) @ 0: ENV [ENV1] Executed ENV1 Code
# KERNEL: UVM_INFO /home/runner/testbench.sv(30) @ 0: ENV [ENV2] Executed ENV2 Code
```

You can also modify Run Options:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/74f0faf0-4c9b-4d84-ac4b-9bac7ef21435)

```
module tb;
  driver drv;
  env e;
  
  initial begin
    drv = new("DRV", null);
    e = new("ENV", null);
    
    // e.set_report_verbosity_level(UVM_HIGH);
	// drv.set_report_id_verbosity("DRV1", UVM_HIGH);
    
    drv.run();
    e.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(14) @ 0: DRV [DRV1] Executed Driver1 Code
# KERNEL: UVM_INFO /home/runner/testbench.sv(15) @ 0: DRV [DRV2] Executed Driver2 Code
# KERNEL: UVM_INFO /home/runner/testbench.sv(29) @ 0: ENV [ENV1] Executed ENV1 Code
# KERNEL: UVM_INFO /home/runner/testbench.sv(30) @ 0: ENV [ENV2] Executed ENV2 Code
```

## Working with Hierarchy
```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path, parent);
  endfunction
  
  task run();
    `uvm_info("DRV", "Executed Driver Code", UVM_HIGH);
  endtask
endclass

////////////////////////////////

class monitor extends uvm_monitor;
  `uvm_component_utils(monitor)
  
  function new (string path, uvm_component parent);
    super.new(path, parent);
  endfunction
  
  task run();
    `uvm_info("MON", "Executed Monitor Code", UVM_HIGH);
  endtask
endclass

////////////////////////////////

class env extends uvm_env;
  `uvm_component_utils(env)
  
  driver drv;
  monitor mon;
  
  function new (string path, uvm_component parent);
    super.new(path, parent);
  endfunction
  
  task run();
    drv = new("DRV", this);
    mon = new("MON", this);
    drv.run();
    mon.run();
  endtask
endclass

////////////////////////////////

module tb;
  env e;
  
  initial begin
    e = new("ENV", null);
    e.set_report_verbosity_level_hier(UVM_HIGH);
    e.run();
  end
endmodule
```

## Other Reporting Macros
- Q: How to print an info message? A warning? An error? A fatal error?
```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path,parent);
  endfunction
  
  task run();
    `uvm_info("DRV", "Informational Message", UVM_NONE);
    `uvm_warning("DRV", "Potential Error");
    `uvm_error("DRV", "Real Error");
    #10;
    `uvm_fatal("DRV", "Simulation cannot continue");
  endtask
endclass

////////////////////////////////

module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    d.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(14) @ 0: DRV [DRV] Informational Message
# KERNEL: UVM_WARNING /home/runner/testbench.sv(15) @ 0: DRV [DRV] Potential Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(16) @ 0: DRV [DRV] Real Error
# KERNEL: UVM_FATAL /home/runner/testbench.sv(18) @ 10: DRV [DRV] Simulation cannot continue
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 10: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    2
# KERNEL: UVM_WARNING :    1
# KERNEL: UVM_ERROR :    1
# KERNEL: UVM_FATAL :    1
# KERNEL: ** Report counts by id
# KERNEL: [DRV]     4
# KERNEL: [UVM/RELNOTES]     1
# KERNEL: 
# RUNTIME: Info: RUNTIME_0068 uvm_root.svh (135): $finish called.
```

## Changing Severity of Macros
- Q: What are the 2 functions that allow us to override report severity (explain the arguments as well)?
```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path,parent);
  endfunction
  
  task run();
    `uvm_info("DRV", "Informational Message", UVM_NONE);
    `uvm_warning("DRV", "Potential Error");
    `uvm_error("DRV", "Real Error");
    #10;
    `uvm_fatal("DRV", "Simulation cannot continue");
  endtask
endclass

////////////////////////////////

module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    d.set_report_severity_override(UVM_FATAL, UVM_ERROR);  // change severity of UVM_FATAL to UVM_ERROR
    d.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(14) @ 0: DRV [DRV] Informational Message
# KERNEL: UVM_WARNING /home/runner/testbench.sv(15) @ 0: DRV [DRV] Potential Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(16) @ 0: DRV [DRV] Real Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(18) @ 10: DRV [DRV] Simulation cannot continue
# KERNEL: Simulation has finished. There are no more test vectors to simulate.
```

```
module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    //d.set_report_severity_override(UVM_FATAL, UVM_ERROR);  // change severity of UVM_FATAL to UVM_ERROR
    d.set_report_severity_id_override(UVM_FATAL, "DRV", UVM_ERROR);
    d.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(14) @ 0: DRV [DRV] Informational Message
# KERNEL: UVM_WARNING /home/runner/testbench.sv(15) @ 0: DRV [DRV] Potential Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(16) @ 0: DRV [DRV] Real Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(18) @ 10: DRV [DRV] Simulation cannot continue DRV1
# KERNEL: UVM_FATAL /home/runner/testbench.sv(20) @ 20: DRV [DRV1] Simulation cannot continue DRV1
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 20: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    2
# KERNEL: UVM_WARNING :    1
# KERNEL: UVM_ERROR :    2
# KERNEL: UVM_FATAL :    1
# KERNEL: ** Report counts by id
# KERNEL: [DRV]     4
# KERNEL: [DRV1]     1
# KERNEL: [UVM/RELNOTES]     1
```

## Changing Associated Actions of Macros
- Q: What are the 8 macros discussed here and what do they do?
- Q: What does set_report_severity_action do? What are its parameters?
- Q: How to get the simulation to display the uvm_info message and then stop the simulation?
- Q: How to get the simulation to display the uvm_fatal, but not stop the simulation?
  
- UVM_NO_ACTION - No action is taken
- UVM_DISPLAY - Sends the report to the standard output
- UVM_LOG - Sends the report to the files(s) for this (severity, id) pair
- UVM_COUNT - Counts the number of reports with the COUNT attribute. When this value reaches max_quit_count, the simulation terminates
- UVM_EXIT - Terminates the simulation immediately
- UVM_CALL_HOOK - Callback the report hook methods
- UVM_STOP - Causes ~$stop~ to be executed, putting the simulation into interactive mode.
- UVM_RM_RECORD - Sends the report to the recorder

```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path,parent);
  endfunction
  
  task run();
    `uvm_info("DRV", "Informational Message", UVM_NONE);
    `uvm_warning("DRV", "Potential Error");
    `uvm_error("DRV", "Real Error");
    #10;
    `uvm_fatal("DRV", "Simulation cannot continue DRV1");
    #10;
    `uvm_fatal("DRV1", "Simulation cannot continue DRV1");
  endtask
endclass

////////////////////////////////

module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    d.set_report_severity_action(UVM_INFO, UVM_NO_ACTION);
    d.run();
  end
endmodule

# KERNEL: UVM_WARNING /home/runner/testbench.sv(15) @ 0: DRV [DRV] Potential Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(16) @ 0: DRV [DRV] Real Error
# KERNEL: UVM_FATAL /home/runner/testbench.sv(18) @ 10: DRV [DRV] Simulation cannot continue DRV1
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 10: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    1
# KERNEL: UVM_WARNING :    1
# KERNEL: UVM_ERROR :    1
# KERNEL: UVM_FATAL :    1
# KERNEL: ** Report counts by id
# KERNEL: [DRV]     3
# KERNEL: [UVM/RELNOTES]     1
```

```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path,parent);
  endfunction
  
  task run();
    `uvm_warning("DRV", "First error");
    `uvm_info("DRV", "Informational Message", UVM_NONE);
    `uvm_warning("DRV", "Potential Error");
    `uvm_error("DRV", "Real Error");
    #10;
    `uvm_fatal("DRV", "Simulation cannot continue DRV1");
    #10;
    `uvm_fatal("DRV1", "Simulation cannot continue DRV1");
  endtask
endclass

////////////////////////////////

module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    d.set_report_severity_action(UVM_INFO, UVM_DISPLAY | UVM_EXIT);  // UVM_INFO will get displayed and then simulation will stop
    d.run();
  end
endmodule

# KERNEL: UVM_WARNING /home/runner/testbench.sv(14) @ 0: DRV [DRV] First error
# KERNEL: UVM_INFO /home/runner/testbench.sv(15) @ 0: DRV [DRV] Informational Message
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 0: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    2
# KERNEL: UVM_WARNING :    1
# KERNEL: UVM_ERROR :    0
# KERNEL: UVM_FATAL :    0
# KERNEL: ** Report counts by id
# KERNEL: [DRV]     2
# KERNEL: [UVM/RELNOTES]     1
```

```
module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    d.set_report_severity_action(UVM_FATAL, UVM_DISPLAY);  // simulation will not stop after a FATAL error, only display the message
    d.run();
  end
endmodule

# KERNEL: UVM_WARNING /home/runner/testbench.sv(14) @ 0: DRV [DRV] First error
# KERNEL: UVM_INFO /home/runner/testbench.sv(15) @ 0: DRV [DRV] Informational Message
# KERNEL: UVM_WARNING /home/runner/testbench.sv(16) @ 0: DRV [DRV] Potential Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(17) @ 0: DRV [DRV] Real Error
# KERNEL: UVM_FATAL /home/runner/testbench.sv(19) @ 10: DRV [DRV] Simulation cannot continue DRV1
# KERNEL: UVM_FATAL /home/runner/testbench.sv(21) @ 20: DRV [DRV1] Simulation cannot continue DRV1
```

## Working with quit_count and UVM_ERROR
- Q: What is the function to set the maximum quit count in the report handler? What are its parameters?
- Q2: How to set it to not have an upper limit?
  
The number of times you have a uvm_error will be stored in a count variable.

```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path,parent);
  endfunction
  
  task run();
    `uvm_info("DRV", "Informational Message", UVM_NONE);
    `uvm_warning("DRV", "Potential Error");
    `uvm_error("DRV", "Real Error");  // default action of uvm_count
    `uvm_error("DRV", "Second Real Error");  // default action of uvm_count
    `uvm_error("DRV", "Third Real Error");  // default action of uvm_count
  endtask
endclass

////////////////////////////////

module tb;
  driver d;
  
  initial begin
    d = new("DRV", null);
    d.set_report_max_quit_count(2);
    d.run();
  end
endmodule

# KERNEL: UVM_INFO /home/runner/testbench.sv(14) @ 0: DRV [DRV] Informational Message
# KERNEL: UVM_WARNING /home/runner/testbench.sv(15) @ 0: DRV [DRV] Potential Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(16) @ 0: DRV [DRV] Real Error
# KERNEL: UVM_ERROR /home/runner/testbench.sv(17) @ 0: DRV [DRV] Second Real Error
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 0: reporter [UVM/REPORT/SERVER] 
# KERNEL: --- UVM Report Summary ---
# KERNEL: 
# KERNEL: Quit count reached!
# KERNEL: Quit count :     2 of     2
# KERNEL: ** Report counts by severity
# KERNEL: UVM_INFO :    2
# KERNEL: UVM_WARNING :    1
# KERNEL: UVM_ERROR :    2
# KERNEL: UVM_FATAL :    0
# KERNEL: ** Report counts by id
# KERNEL: [DRV]     4
# KERNEL: [UVM/RELNOTES]     1
```
- A2: Default value of 0.

## Working with log file
- Q: How to declare the file descriptor ID and then open the file in write mode?
- Q: How to get the simulation to print uvm_info messages to a log file?

```
`include "uvm_macros.svh"
import uvm_pkg::*;

////////////////////////////////

class driver extends uvm_driver;
  `uvm_component_utils(driver)
  
  function new (string path, uvm_component parent);
    super.new(path,parent);
  endfunction
  
  task run();
    `uvm_info("DRV", "Informational Message", UVM_NONE);
    `uvm_warning("DRV", "Potential Error");
    `uvm_error("DRV", "Real Error");  // default action of uvm_count
    `uvm_error("DRV", "Second Real Error");  // default action of uvm_count
    `uvm_error("DRV", "Third Real Error");  // default action of uvm_count
  endtask
endclass

////////////////////////////////

module tb;
  driver d;
  int file;
  
  initial begin
    file = $fopen("log.txt", "w");
    d = new("DRV", null);
    d.set_report_default_file(file);
    d.set_report_severity_action(UVM_INFO, UVM_DISPLAY | UVM_LOG);
    d.set_report_severity_action(UVM_WARNING, UVM_DISPLAY | UVM_LOG);
    d.set_report_severity_action(UVM_ERROR, UVM_DISPLAY | UVM_LOG);
    d.run();
    #10;
    $fclose(file);
  end
endmodule
```
