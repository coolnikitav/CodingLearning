# UVM_PHASES

## Fundamentals of Phases
- Q: What do phases handle?
- A:
  - Configure TB env
  - System Reset
  - Applying stimulus to DUT
  - Comparing Response with golden data
  - Generating report

## Classification of Phases: Methods Used
- Q: Give example of a phase that consumes time. The doesn't consume time
  
- Phases
  - Consume time
    - Task
  - Do not consume time
    - Function, super
 
- A: Does not consume time: creating object or class. This method should not consume time to make sure all objects are ready at 0 nSec
- A: Consumes times: applying stimulus to DUT on valid clock edge. If we apply all the stimulus at 0 nSec, we will get unexpected behavior.

## Classification of Phases: Specific Purposes
- Q: What are the 3 types of phases? Give at least 2 examples of each type.

- Phase
  - Construction phase
    - build_phase - create object of a class
    - connect_phase - perform connection of a component in a TLM (transaction-level modeling)
    - end_of_elaboration_phase - adjust hierarchy of a component
    - start_of_simulation - configure env before applying stimulus
  - run_phase - generation and application of stimulus, waiting for results
    - reset_phase, pre_reset_phase, post_reset_phase - system reset
    - configure_phase, pre_configure_phase, post_configure_phase - set variables to certain values before generation
    - main_phase, pre_main_phase, post_main_phase - generating stimulus + collecting response
    - shutdown_phase, pre_shutdown_phase, post_shutdown_phase - make sure that all stimuli is correctly applied to the DUT and got a response
  - cleanup phase - collect and report data, check that coverage goals are achieved
    - extract_phase
    - check_phase
    - report_phase
    - final_phase

## How to Override Phases
- Phases
  - Do not consume time (function + super)
    - build phase
    - connect phase
    - end of elaboration
    - start of simulation
    - extract
    - check
    - report
    - final
  - Consume time (task)
    - run phase
   
Phases are only allowed in UVM_COMPONENT

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class test extends uvm_test;
  `uvm_component_utils(test)
  
  function new (string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  /* 
   *  Construction Phases
   */
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("test", "Build Phase Executed", UVM_NONE);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("test", "Connect Phase Executed", UVM_NONE);
  endfunction
  
  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    `uvm_info("test", "End of Elaboration Phase Executed", UVM_NONE);
  endfunction
  
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    `uvm_info("test", "Start of Simulation Phase Executed", UVM_NONE);
  endfunction
  
  /*
   *  Main Phases
   */
  task run_phase(uvm_phase phase);
    `uvm_info("test", "Run Phase", UVM_NONE);
  endtask
  
  /*
   *  Cleanup Phases
   */
  function void extract_phase(uvm_phase phase);
    super.extract_phase(phase);
    `uvm_info("test", "Extract Phase", UVM_NONE);
  endfunction
  
  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `uvm_info("test", "Check Phase", UVM_NONE);
  endfunction
  
  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("test", "Report Phase", UVM_NONE);
  endfunction
  
  function void final_phase(uvm_phase phase);
    super.final_phase(phase);
    `uvm_info("test", "Final Phase", UVM_NONE);
  endfunction
endclass
```

## Understanding execution of build_phase in multiple components
- Q1: What does top-down approach mean?
- Q2: What does bottom-up approach mean?
  
- A1: Test -> ENV -> Agent -> Drv/Mon
- A2: Drv/Mon -> Agent -> Env -> Test

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class driver extends uvm_driver;
  `uvm_component_utils(driver)  // register to a factory
  
  function new (string path = "driver", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("driver", "Driver Build Phase Executed", UVM_NONE);
  endfunction
endclass
  
///////////////////////////////////////

class monitor extends uvm_monitor;
  `uvm_component_utils(monitor)  // register to a factory
  
  function new (string path = "monitor", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("monitor", "Monitor Build Phase Executed", UVM_NONE);
  endfunction
endclass

///////////////////////////////////////

class env extends uvm_env;
  `uvm_component_utils(env)
  
  driver drv;
  monitor mon;
  
  function new (string path = "env", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("env", "Env Build Phase Executed", UVM_NONE);
    drv = driver::type_id::create("drv", this);
    mon = monitor::typed_id::create("mon", this);
  endfunction
endclass

///////////////////////////////////////

class test extends uvm_test;
  `uvm_component_utils(test)
  
  env e;
  
  function new (string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("test", "Test Build Phase Executed", UVM_NONE);
    e = env::type_id::create("e", this);
  endfunction
endclass

///////////////////////////////////////

module tb;
  initial begin
    $display("5");
    run_test("test");
  end
endmodule
```

## Understanding Execution of connect_phase
connect_phase executes in top-down fashion, while the rest of the phases execute in bottom-up

## Execution of Multiple instance phases
```
drv = driver::type_id::create("drv", this);
mon = monitor::typed_id::create("mon", this);
```

They are executed in lexicographical order of the ASCII table

## Raising Objection
Without raising an objection, simulator will exit after "Reset started" and not wait until "Reset completed".
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class comp extends uvm_component;
  `uvm_component_utils(comp)
  
  function new (string path = "comp", uvm_component parent = null);
    super.new(path, parent)        
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);  // this phase
    `uvm_info("comp","Reset started", UVM_NONE);
    #100;
    `uvm_info("comp","Reset completed", UVM_NONE);
    phase.drop_objection(this);
  endtask
endclass

module tb;
  initial begin
    run_test("comp");
  end
endmodule
```

## How Time Consuming Phases Work in a Single Component
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class comp extends uvm_component;
  `uvm_component_utils(comp)
  
  function new (string path = "comp", uvm_component parent = null);
    super.new(path, parent)        
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);  // this phase
    `uvm_info("comp","Reset phase started", UVM_NONE);
    #10;
    `uvm_info("comp","Reset phase completed", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("comp","Main phase started", UVM_NONE);
    #100;
    `uvm_info("comp","Main phase completed", UVM_NONE);
    phase.drop_objection(this);
  endtask
endclass

module tb;
  initial begin
    run_test("comp");
  end
endmodule
```

Main phase doesn't start at 0:
```
@0: [comp] Reset phase started
@10: [comp] Reset phase completed
@10: [mon] Main phase started
@110: [mon] Main phase ended
```

## Time Consuming Phases in Multiple Components
```
`include "uvm_macros.svh"
import uvm_pkg::*;
 
 
 
 
///////////////////////////////////////////////////////////////
 
class driver extends uvm_driver;
  `uvm_component_utils(driver) 
  
  
  function new(string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("drv", "Driver Reset Started", UVM_NONE);
    #100;
    `uvm_info("drv", "Driver Reset Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  
  task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("drv", "Driver Main Phase Started", UVM_NONE);
    #100;
    `uvm_info("drv", "Driver Main Phase Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  
 
  
endclass
 
///////////////////////////////////////////////////////////////
 
class monitor extends uvm_monitor;
  `uvm_component_utils(monitor) 
  
  
  function new(string path = "monitor", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("mon", "Monitor Reset Started", UVM_NONE);
     #300;
    `uvm_info("mon", "Monitor Reset Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  
  task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("mon", "Monitor Main Phase Started", UVM_NONE);
     #400;
    `uvm_info("mon", "Monitor Main Phase Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
endclass
 
////////////////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
  `uvm_component_utils(env) 
  
  driver d;
  monitor m;
  
  function new(string path = "env", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    d = driver::type_id::create("d", this);
    m = monitor::type_id::create("m", this);
  endfunction
  
 
  
endclass
 
 
 
////////////////////////////////////////////////////////////////////////////////////////
 
class test extends uvm_test;
  `uvm_component_utils(test)
  
  env e;
  
  function new(string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("e", this);
  endfunction
  
  
endclass
 
///////////////////////////////////////////////////////////////////////////
module tb;
  
  initial begin
    run_test("test");
  end
  
 
endmodule
```

```
@0: Monitor reset started
@0: Driver reset started
@100: Driver reset ended
@300: Monitor reset ended
@300: Monitor main phase started
@300: Driver main phase started
@400: Driver main phase ended
@700: Monitor main phase ended
```

## Timeout
Timeout is the maximum absolute simulation time allowed before a FATAL occurs. Default value is 9200sec

```
module tb;
  initial begin
    uvm_top.set_timeout(100ns,0);
    run_test("comp");
  end
endmodule
```

## Drain time: Individual Component
Drain time indicates how long the simulator should stay in a phase

```
`include "uvm_macros.svh"
import uvm_pkg::*;
/////Default Timeout = 9200sec
 
 
class comp extends uvm_component;
  `uvm_component_utils(comp)
  
 
  function new(string path = "comp", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("comp","Reset Started", UVM_NONE);
     #10;
    `uvm_info("comp","Reset Completed", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  task main_phase(uvm_phase phase);
    phase.phase_done.set_drain_time(this,200);
    phase.raise_objection(this);
    `uvm_info("mon", " Main Phase Started", UVM_NONE);
    #100;
    `uvm_info("mon", " Main Phase Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  task post_main_phase(uvm_phase phase);
    `uvm_info("mon", " Post-Main Phase Started", UVM_NONE);
  endtask
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase); 
  endfunction
  
  
endclass
 
///////////////////////////////////////////////////////////////////////////
module tb;
  
  initial begin
   // uvm_top.set_timeout(100ns, 0);
    
    run_test("comp");
  end
  
 
endmodule
```

```
@0: Reset Started
@10: Reset Completed
@10: Main Phase Started
@110: Main Phase Ended
@310: Post-Main Phase Started
```

## Drain Time: Multiple Components
```
`include "uvm_macros.svh"
import uvm_pkg::*;
 
 
 
 
///////////////////////////////////////////////////////////////
 
class driver extends uvm_driver;
  `uvm_component_utils(driver) 
  
  
  function new(string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("drv", "Driver Reset Started", UVM_NONE);
    #100;
    `uvm_info("drv", "Driver Reset Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  
  task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("drv", "Driver Main Phase Started", UVM_NONE);
    #100;
    `uvm_info("drv", "Driver Main Phase Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  task post_main_phase(uvm_phase phase);
    `uvm_info("drv", "Driver Post-Main Phase Started", UVM_NONE);  
  endtask
  
 
  
endclass
 
///////////////////////////////////////////////////////////////
 
class monitor extends uvm_monitor;
  `uvm_component_utils(monitor) 
  
  
  function new(string path = "monitor", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("mon", "Monitor Reset Started", UVM_NONE);
     #150;
    `uvm_info("mon", "Monitor Reset Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  
  task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("mon", "Monitor Main Phase Started", UVM_NONE);
     #200;
    `uvm_info("mon", "Monitor Main Phase Ended", UVM_NONE);
    phase.drop_objection(this);
  endtask
  
  task post_main_phase(uvm_phase phase);
    `uvm_info("mon", "Monitor Post-Main Phase Started", UVM_NONE);  
  endtask
  
endclass
 
////////////////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
  `uvm_component_utils(env) 
  
  driver d;
  monitor m;
  
  function new(string path = "env", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    d = driver::type_id::create("d", this);
    m = monitor::type_id::create("m", this);
  endfunction
  
 
  
endclass
 
 
 
////////////////////////////////////////////////////////////////////////////////////////
 
class test extends uvm_test;
  `uvm_component_utils(test)
  
  env e;
  
  function new(string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("e", this);
  endfunction
  
 function void end_of_elaboration_phase(uvm_phase phase);
   uvm_phase main_phase;
   super.end_of_elaboration_phase(phase);
    main_phase = phase.find_by_name("main", 0);
    main_phase.phase_done.set_drain_time(this, 100);
  endfunction
  
  
endclass
 
///////////////////////////////////////////////////////////////////////////
module tb;
  
  initial begin
    run_test("test");
  end
  
 
endmodule
```
```
@0: Monitor reset started
@0: Driver reset started
@100: Driver reset ended
@150: Monitor reset ended
@150: Monitor main phase started
@150: Driver main phase started
@250: Driver main phase ended
@350: Monitor main phase ended
@450: Monitor post-main phase started
@450: Driver post-main phase started
```

## Phase Debug
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/bc5fd6bc-4bb0-4d28-950a-2468d8952639)

Prints more elaborate debugging statements about the phases.

## Objection Debug
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f6d7af9-65bb-4bf7-ac0a-885d6841daf1)

Prints more elaborate debugging statements about the objections.
