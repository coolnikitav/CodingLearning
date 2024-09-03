# Different Register Method

## Types of Predictor: Implicit Predictor
We do not have a predictor block explicitely defined.

![image](https://github.com/user-attachments/assets/e35ce1e4-d035-4043-91ea-2c6f6bdd8fc0)

![image](https://github.com/user-attachments/assets/6906fc29-2772-4f68-831a-259e0a129db8)

![image](https://github.com/user-attachments/assets/e44d2380-41f8-4ec8-896f-1c1415834611)


Sequence:
- Generate reg data
- Adapter convert reg_tx to bus_tx
- Sent to driver
- Driver apply stimuli to DUT
- Driver collect response
- reg model use response to update desire/mirror value

## Types of Predictor: Explicit Predictor
We have a predictor block explicitely defined.

## Types of Predictor: Passive Predictor
reg model is not connected to the sequencer

## Driver Sequencer Communication
```
`include "uvm_macros.svh"
import uvm_pkg::*;
 
 
///////////////////////transaction class
class transaction extends uvm_sequence_item;
  rand bit[3:0] addr;
  rand bit[3:0] data;
  
  `uvm_object_utils(transaction)
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
endclass
 
///////////////////////generator
 
class generator extends uvm_sequence #(transaction);
  `uvm_object_utils(generator)
  
    transaction tr;
  
  function new (string name = "generator");
    super.new(name);
  endfunction
 
  task body();
    tr = transaction::type_id::create("tr");
    wait_for_grant();
    assert(tr.randomize());
    `uvm_info("SEQ", $sformatf("Sending TX to SEQR: addr = %0d  data = %0d", tr.addr, tr.data),UVM_LOW); 
    send_request(tr);
    wait_for_item_done();
    get_response(tr);
    `uvm_info("SEQ", $sformatf("After get_response: addr = %0d  data = %0d", tr.addr, tr.data), UVM_LOW);
  endtask
endclass
 
/////////////////////////////////driver
 
 
class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)
  
  transaction tr;
  
  
  function new(string name = "driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
 
  
  task run_phase (uvm_phase phase);
    forever 
      begin
        seq_item_port.get_next_item(tr);
        `uvm_info("DRV", $sformatf("Recv. TX from SEQR addr = %0d data = %0d",tr.addr, tr.data), UVM_LOW);
         #100; 
        `uvm_info("DRV", $sformatf("Applied Stimuli to DUT -> Sending REQ response to SEQR"), UVM_LOW);
        seq_item_port.item_done(tr);
      end
  endtask
  
  
endclass
 
 
///////////////////////////////////////////////////// sequencer
 
 
class sequencer extends uvm_sequencer #(transaction);
  `uvm_component_utils(sequencer)
  
  function new(string name = "sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
endclass
 
////////////////////////////////////////////agent
 
class agent extends uvm_agent;
   `uvm_component_utils(agent)
  
  driver drv;
  sequencer seqr;
  
 
  
  function new(string name = "agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv = driver::type_id::create("drv", this);
    seqr = sequencer::type_id::create("seqr", this);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction
  
  
endclass
 
 
//////////////////////////////////////////////////// env
class env extends uvm_agent;
  `uvm_component_utils(env)
 
  
  agent agt;
  
  function new(string name = "env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agt = agent::type_id::create("agt", this);
  endfunction
  
endclass
 
//////////////////////////////////////////////////////////test
 
class test extends uvm_test;
  `uvm_component_utils(test)
  
  
  env e;
  generator gen;
 
 
  
  function new(string name = "test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("e", this);
    gen = generator::type_id::create("gen");    
 
  endfunction
 
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    gen.start(e.agt.seqr);
    phase.drop_objection(this);
  endtask
endclass
 
 
/////////////////////////////////////////////
 
module tb;
  initial begin
    run_test("test");
  end
endmodule

# KERNEL: UVM_INFO @ 0: reporter [RNTST] Running test test...
# KERNEL: UVM_INFO /home/runner/testbench.sv(33) @ 0: uvm_test_top.e.agt.seqr@@gen [SEQ] Sending TX to SEQR: addr = 14  data = 6
# KERNEL: UVM_INFO /home/runner/testbench.sv(60) @ 0: uvm_test_top.e.agt.drv [DRV] Recv. TX from SEQR addr = 14 data = 6
# KERNEL: UVM_INFO /home/runner/testbench.sv(62) @ 100: uvm_test_top.e.agt.drv [DRV] Applied Stimuli to DUT -> Sending REQ response to SEQR
# KERNEL: UVM_INFO /home/runner/testbench.sv(37) @ 100: uvm_test_top.e.agt.seqr@@gen [SEQ] After get_response: addr = 14  data = 6
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_objection.svh(1271) @ 100: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
# KERNEL: UVM_INFO /home/build/vlib1/vlib/uvm-1.2/src/base/uvm_report_server.svh(869) @ 100: reporter [UVM/REPORT/SERVER] 
```

## Understanding Design
