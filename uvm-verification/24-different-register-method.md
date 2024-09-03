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

## Understanding Desigerd and Mirrored values
- Desired: Value of register for next transaction allows to specify value before write
- Mirrored: Current known state of hardware register. Updated at the end of each read/write

```
Desired: 0, Mirrored: 0, DUT_reg: 0
Set(2)
Desired: 2, Mirrored: 0, DUT_reg: 0
Update
Desired: 2, Mirrored: 2, DUT_reg: 2
```

## Different Register Methods
Methods before transaction
- Desired value
  - Set
  - Get
- Mirrored value
  - get_mirrored_value
 
Methods after transaction
- Desired value + mirroried value
  - Frontdoor access
    - write
    - reda
    - update
    - mirror
    - predict
    - randomize
  - Backdoor access
    - peek
    - poke

## Working with Desired Value
- get does not actually read the value of the register in the design, only the desired value
- set only sets the desired value, not the actual value
- update updates the content of the register in the design to match the desired value

```
import uvm_pkg::*;
`include "uvm_macros.svh"
 
//////////////////transaction class
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
 
       bit [7:0] din;
       bit       wr;
       bit       addr;
       bit       rst;
       bit [7:0] dout;   
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
 
 
endclass
 
///////////////////////////////////////////////////////
////////////////////////driver 
 
class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)
 
  transaction tr;
  virtual top_if tif;
 
  function new(input string path = "driver", uvm_component parent = null);
    super.new(path,parent);
  endfunction
 
  virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
    if(!uvm_config_db#(virtual top_if)::get(this,"","tif",tif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  ///////////////reset DUT at the start
  task reset_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b1;
    tif.wr   <= 1'b0;
    tif.din  <= 8'h00;
    tif.addr <= 1'b0;
    repeat(5)@(posedge tif.clk);
    `uvm_info("DRV", "System Reset", UVM_NONE);
    tif.rst  <= 1'b0;
  endtask
  
  //////////////drive DUT
  
  task drive_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b0;
    tif.wr   <= tr.wr;
    tif.addr <= tr.addr;
    if(tr.wr == 1'b1)
       begin
           tif.din <= tr.din;
           @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Write -> Wdata : %0d",tif.din), UVM_NONE);
       end
      else
       begin  
           tr.dout <= tif.dout;
           @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
       end    
  endtask
  
  
  
  ///////////////main task of driver
  
   virtual task run_phase(uvm_phase phase);
      tr = transaction::type_id::create("tr");
     forever begin
        seq_item_port.get_next_item(tr);
        drive_dut();
        seq_item_port.item_done();  
      end
   endtask
 
endclass
 
////////////////////////////////////////////////////////////////////////////////
///////////////////////agent class
 
 
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this); 
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
   d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
////////////////////////////////////////////////////////////////////////////////////////
 
 
 
//////////////////////building reg model
 
////////////////////////
 
 
class temp_reg extends uvm_reg;
  `uvm_object_utils(temp_reg)
   
 
  rand uvm_reg_field temp;
 
  
  function new (string name = "temp_reg");
    super.new(name,8,UVM_NO_COVERAGE); 
  endfunction
 
 
  
  function void build; 
    
 
    temp = uvm_reg_field::type_id::create("temp");   
    // Configure
    temp.configure(  .parent(this), 
                     .size(8), 
                     .lsb_pos(0), 
                     .access("RW"),  
                     .volatile(0), 
                     .reset(0), 
                     .has_reset(1), 
                     .is_rand(1), 
                     .individually_accessible(1)); 
 
    
  endfunction
  
endclass
 
 
//////////////////////////////////////creating reg block
 
 
class top_reg_block extends uvm_reg_block;
  `uvm_object_utils(top_reg_block)
  
 
  rand temp_reg 	temp_reg_inst; 
  
 
  function new (string name = "top_reg_block");
    super.new(name, build_coverage(UVM_NO_COVERAGE));
  endfunction
 
 
  function void build;
    
 
    temp_reg_inst = temp_reg::type_id::create("temp_reg_inst");
    temp_reg_inst.build();
    temp_reg_inst.configure(this);
 
 
    default_map = create_map("default_map", 'h0, 1, UVM_LITTLE_ENDIAN); // name, base, nBytes
    default_map.add_reg(temp_reg_inst	, 'h0, "RW");  // reg, offset, access
    
    lock_model();
  endfunction
endclass
 
 
/////////////////////////////////////////////////////////////////////////////////////
 
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [7:0] rdata;
     
    ////////////////////////initial value
    rdata = regmodel.temp_reg_inst.get();
    `uvm_info("SEQ", $sformatf("Desired Value : %0d", rdata), UVM_NONE);
    
    ////////////////// update desire value
    regmodel.temp_reg_inst.set(8'h11);
    
    ///////////////// get desire value
     rdata = regmodel.temp_reg_inst.get();
    `uvm_info("SEQ", $sformatf("Desired Value : %0d", rdata), UVM_NONE);
 
    ///////////////// call write method 
    regmodel.temp_reg_inst.update(status);
 
 
  endtask
  
  
endclass
 
////////////////////////////////////////////////////////////////////////
///////////////////////reg adapter
 
class top_adapter extends uvm_reg_adapter;
  `uvm_object_utils (top_adapter)
 
  //---------------------------------------
  // Constructor 
  //--------------------------------------- 
  function new (string name = "top_adapter");
      super.new (name);
   endfunction
  
  //---------------------------------------
  // reg2bus method 
  //--------------------------------------- 
  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    transaction tr;    
    tr = transaction::type_id::create("tr");
    
    tr.wr    = (rw.kind == UVM_WRITE);
    tr.addr  = rw.addr;
    
    if(tr.wr == 1'b1) tr.din = rw.data;
    
    return tr;
  endfunction
 
  //---------------------------------------
  // bus2reg method 
  //--------------------------------------- 
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
 
    rw.kind = tr.wr ? UVM_WRITE : UVM_READ;
    rw.data = tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
 
 
 
 
////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
  
  agent          agent_inst;
  top_reg_block  regmodel;   
  top_adapter    adapter_inst;
  
  `uvm_component_utils(env)
  
  //--------------------------------------- 
  // constructor
  //---------------------------------------
  function new(string name = "env", uvm_component parent);
    super.new(name, parent);
  endfunction : new
 
  //---------------------------------------
  // build_phase - create the components
  //---------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent_inst = agent::type_id::create("agent_inst", this);
    regmodel   = top_reg_block::type_id::create("regmodel", this);
    regmodel.build();
    
    
    adapter_inst = top_adapter::type_id::create("adapter_inst",, get_full_name());
  endfunction 
  
 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    regmodel.default_map.set_sequencer( .sequencer(agent_inst.seqr), .adapter(adapter_inst) );
    regmodel.default_map.set_base_addr(0);        
  endfunction 
 
endclass
 
//////////////////////////////////////////////////////////////////////////////////////////////////
 
 
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
env e;
top_reg_seq trseq;
 
 
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e      = env::type_id::create("env",this);
   trseq  = top_reg_seq::type_id::create("trseq");
  
  // e.set_config_int( "*", "include_coverage", 0 );
endfunction
 
virtual task run_phase(uvm_phase phase);
  
  phase.raise_objection(this);
  
  trseq.regmodel = e.regmodel;
  trseq.start(e.agent_inst.seqr);
  phase.drop_objection(this);
  
  phase.phase_done.set_drain_time(this, 200);
endtask
endclass
 
//////////////////////////////////////////////////////////////
 
 
module tb;
  
    
  top_if tif();
    
  top dut (tif.clk, tif.rst, tif.wr, tif.addr, tif.din, tif.dout);
 
  
  initial begin
   tif.clk <= 0;
  end
 
  always #10 tif.clk = ~tif.clk;
 
  
  
  initial begin
    uvm_config_db#(virtual top_if)::set(null, "*", "tif", tif);
    
    uvm_config_db#(int)::set(null,"*","include_coverage", 0); //to remove include coverage message
 
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```

## Working with Mirrored Value
- mirror variable stores the current know state of the hardware register

```
import uvm_pkg::*;
`include "uvm_macros.svh"
 
//////////////////transaction class
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
 
       bit [7:0] din;
       bit       wr;
       bit       addr;
       bit       rst;
       bit [7:0] dout;   
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
 
 
endclass
 
///////////////////////////////////////////////////////
////////////////////////driver 
 
class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)
 
  transaction tr;
  virtual top_if tif;
 
  function new(input string path = "driver", uvm_component parent = null);
    super.new(path,parent);
  endfunction
 
  virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
    if(!uvm_config_db#(virtual top_if)::get(this,"","tif",tif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  ///////////////reset DUT at the start
  task reset_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b1;
    tif.wr   <= 1'b0;
    tif.din  <= 8'h00;
    tif.addr <= 1'b0;
    repeat(5)@(posedge tif.clk);
    `uvm_info("DRV", "System Reset", UVM_NONE);
    tif.rst  <= 1'b0;
  endtask
  
  //////////////drive DUT
  
  task drive_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b0;
    tif.wr   <= tr.wr;
    tif.addr <= tr.addr;
    if(tr.wr == 1'b1)
       begin
           tif.din <= tr.din;
           @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Write -> Wdata : %0d",tif.din), UVM_NONE);
       end
      else
       begin  
           tr.dout <= tif.dout;
           @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
       end    
  endtask
  
  
  
  ///////////////main task of driver
  
   virtual task run_phase(uvm_phase phase);
      tr = transaction::type_id::create("tr");
     forever begin
        seq_item_port.get_next_item(tr);
        drive_dut();
        seq_item_port.item_done();  
      end
   endtask
 
endclass
 
////////////////////////////////////////////////////////////////////////////////
///////////////////////agent class
 
 
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this); 
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
   d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
////////////////////////////////////////////////////////////////////////////////////////
 
 
 
//////////////////////building reg model
 
////////////////////////
 
 
class temp_reg extends uvm_reg;
  `uvm_object_utils(temp_reg)
   
 
  rand uvm_reg_field temp;
 
  
  function new (string name = "temp_reg");
    super.new(name,8,UVM_NO_COVERAGE); 
  endfunction
 
 
  
  function void build; 
    
 
    temp = uvm_reg_field::type_id::create("temp");   
    // Configure
    temp.configure(  .parent(this), 
                     .size(8), 
                     .lsb_pos(0), 
                     .access("RW"),  
                     .volatile(0), 
                     .reset(0), 
                     .has_reset(1), 
                     .is_rand(1), 
                     .individually_accessible(1)); 
 
    
  endfunction
  
endclass
 
 
//////////////////////////////////////creating reg block
 
 
class top_reg_block extends uvm_reg_block;
  `uvm_object_utils(top_reg_block)
  
 
  rand temp_reg 	temp_reg_inst; 
  
 
  function new (string name = "top_reg_block");
    super.new(name, build_coverage(UVM_NO_COVERAGE));
  endfunction
 
 
  function void build;
    
 
    temp_reg_inst = temp_reg::type_id::create("temp_reg_inst");
    temp_reg_inst.build();
    temp_reg_inst.configure(this);
 
 
    default_map = create_map("default_map", 'h0, 1, UVM_LITTLE_ENDIAN); // name, base, nBytes
    default_map.add_reg(temp_reg_inst	, 'h0, "RW");  // reg, offset, access
    
    
    default_map.set_auto_predict(1);
    
    lock_model();
  endfunction
endclass
 
 
/////////////////////////////////////////////////////////////////////////////////////
 
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [7:0] rdata,rdata_m;
     
    ////////////////////////initial value
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Initial Value -> Desired Value : %0d and Mirrored Value : %0d", rdata, rdata_m), UVM_NONE);
    
    ////////////////// update desire value
    regmodel.temp_reg_inst.set(8'h11);
    
    ///////////////// get desire value
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("After Set -> Desired Value : %0d and Mirrored Value : %0d", rdata, rdata_m), UVM_NONE);
 
    ///////////////// call write method 
    regmodel.temp_reg_inst.update(status);
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("After Tx to DUT -> Desired Value : %0d and Mirrored Value : %0d", rdata, rdata_m), UVM_NONE);
 
 
  endtask
  
  
endclass
 
////////////////////////////////////////////////////////////////////////
///////////////////////reg adapter
 
class top_adapter extends uvm_reg_adapter;
  `uvm_object_utils (top_adapter)
 
  //---------------------------------------
  // Constructor 
  //--------------------------------------- 
  function new (string name = "top_adapter");
      super.new (name);
   endfunction
  
  //---------------------------------------
  // reg2bus method 
  //--------------------------------------- 
  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    transaction tr;    
    tr = transaction::type_id::create("tr");
    
    tr.wr    = (rw.kind == UVM_WRITE);
    tr.addr  = rw.addr;
    
    if(tr.wr == 1'b1) tr.din = rw.data;
    
    return tr;
  endfunction
 
  //---------------------------------------
  // bus2reg method 
  //--------------------------------------- 
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
 
    rw.kind = tr.wr ? UVM_WRITE : UVM_READ;
    rw.data = tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
 
 
 
 
////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
  
  agent          agent_inst;
  top_reg_block  regmodel;   
  top_adapter    adapter_inst;
  
  `uvm_component_utils(env)
  
  //--------------------------------------- 
  // constructor
  //---------------------------------------
  function new(string name = "env", uvm_component parent);
    super.new(name, parent);
  endfunction : new
 
  //---------------------------------------
  // build_phase - create the components
  //---------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent_inst = agent::type_id::create("agent_inst", this);
    regmodel   = top_reg_block::type_id::create("regmodel", this);
    regmodel.build();
    
    
    adapter_inst = top_adapter::type_id::create("adapter_inst",, get_full_name());
  endfunction 
  
 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    regmodel.default_map.set_sequencer( .sequencer(agent_inst.seqr), .adapter(adapter_inst) );
    regmodel.default_map.set_base_addr(0);        
  endfunction 
 
endclass
 
//////////////////////////////////////////////////////////////////////////////////////////////////
 
 
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
env e;
top_reg_seq trseq;
 
 
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e      = env::type_id::create("env",this);
   trseq  = top_reg_seq::type_id::create("trseq");
  
  // e.set_config_int( "*", "include_coverage", 0 );
endfunction
 
virtual task run_phase(uvm_phase phase);
  
  phase.raise_objection(this);
  
  trseq.regmodel = e.regmodel;
  trseq.start(e.agent_inst.seqr);
  phase.drop_objection(this);
  
  phase.phase_done.set_drain_time(this, 200);
endtask
endclass
 
//////////////////////////////////////////////////////////////
 
 
module tb;
  
    
  top_if tif();
    
  top dut (tif.clk, tif.rst, tif.wr, tif.addr, tif.din, tif.dout);
 
  
  initial begin
   tif.clk <= 0;
  end
 
  always #10 tif.clk = ~tif.clk;
 
  
  
  initial begin
    uvm_config_db#(virtual top_if)::set(null, "*", "tif", tif);
    
    uvm_config_db#(int)::set(null,"*","include_coverage", 0); //to remove include coverage message
 
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```

## Understanding predict and mirror
- predict updates both the desired and mirrored values
- mirror reads the register and updates its mirror value

```
import uvm_pkg::*;
`include "uvm_macros.svh"
 
//////////////////transaction class
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
 
       bit [7:0] din;
       bit       wr;
       bit       addr;
       bit       rst;
       bit [7:0] dout;   
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
 
 
endclass
 
///////////////////////////////////////////////////////
////////////////////////driver 
 
class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)
 
  transaction tr;
  virtual top_if tif;
 
  function new(input string path = "driver", uvm_component parent = null);
    super.new(path,parent);
  endfunction
 
  virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
    if(!uvm_config_db#(virtual top_if)::get(this,"","tif",tif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  ///////////////reset DUT at the start
  task reset_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b1;
    tif.wr   <= 1'b0;
    tif.din  <= 8'h00;
    tif.addr <= 1'b0;
    repeat(5)@(posedge tif.clk);
    `uvm_info("DRV", "System Reset", UVM_NONE);
    tif.rst  <= 1'b0;
  endtask
  
  //////////////drive DUT
  
  task drive_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b0;
    tif.wr   <= tr.wr;
    tif.addr <= tr.addr;
    if(tr.wr == 1'b1)
       begin
           tif.din <= tr.din;
         repeat(2) @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Write -> Wdata : %0d",tif.din), UVM_NONE);
       end
      else
       begin  
          repeat(2) @(posedge tif.clk);
           tr.dout = tif.dout;
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
       end    
  endtask
  
  
  
  ///////////////main task of driver
  
   virtual task run_phase(uvm_phase phase);
      tr = transaction::type_id::create("tr");
     forever begin
        seq_item_port.get_next_item(tr);
        drive_dut();
        seq_item_port.item_done();  
      end
   endtask
 
endclass
 
////////////////////////////////////////////////////////////////////////////////
///////////////////////agent class
 
 
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this); 
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
   d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
////////////////////////////////////////////////////////////////////////////////////////
 
 
 
//////////////////////building reg model
 
////////////////////////
 
 
class temp_reg extends uvm_reg;
  `uvm_object_utils(temp_reg)
   
 
  rand uvm_reg_field temp;
 
  
  function new (string name = "temp_reg");
    super.new(name,8,UVM_NO_COVERAGE); 
  endfunction
 
 
  
  function void build; 
    
 
    temp = uvm_reg_field::type_id::create("temp");   
    // Configure
    temp.configure(  .parent(this), 
                     .size(8), 
                     .lsb_pos(0), 
                     .access("RW"),  
                     .volatile(0), 
                     .reset(0), 
                     .has_reset(1), 
                     .is_rand(1), 
                     .individually_accessible(1)); 
 
    
  endfunction
  
endclass
 
 
//////////////////////////////////////creating reg block
 
 
class top_reg_block extends uvm_reg_block;
  `uvm_object_utils(top_reg_block)
  
 
  rand temp_reg 	temp_reg_inst; 
  
 
  function new (string name = "top_reg_block");
    super.new(name, build_coverage(UVM_NO_COVERAGE));
  endfunction
 
 
  function void build;
    
 
    temp_reg_inst = temp_reg::type_id::create("temp_reg_inst");
    temp_reg_inst.build();
    temp_reg_inst.configure(this);
 
 
    default_map = create_map("default_map", 'h0, 1, UVM_LITTLE_ENDIAN); // name, base, nBytes
    default_map.add_reg(temp_reg_inst	, 'h0, "RW");  // reg, offset, access
    
    
    default_map.set_auto_predict(1);
    
    lock_model();
  endfunction
endclass
 
 
/////////////////////////////////////////////////////////////////////////////////////
 
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [7:0] rdata,rdata_m;
    
    
    
     regmodel.temp_reg_inst.write(status,5'h10);
     rdata =   regmodel.temp_reg_inst.get();
     rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Mir : %0d Des : %0d ", rdata_m, rdata), UVM_NONE);
   
     
     regmodel.temp_reg_inst.predict(5'h05);
     rdata =   regmodel.temp_reg_inst.get();
     rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Mir : %0d Des : %0d ", rdata_m, rdata), UVM_NONE);
   
    regmodel.temp_reg_inst.mirror(status,UVM_NO_CHECK);
     rdata =   regmodel.temp_reg_inst.get();
     rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Mir : %0d Des : %0d ", rdata_m, rdata), UVM_NONE);
  
    
  
  endtask
  
  
endclass
 
////////////////////////////////////////////////////////////////////////
///////////////////////reg adapter
 
class top_adapter extends uvm_reg_adapter;
  `uvm_object_utils (top_adapter)
 
  //---------------------------------------
  // Constructor 
  //--------------------------------------- 
  function new (string name = "top_adapter");
      super.new (name);
   endfunction
  
  //---------------------------------------
  // reg2bus method 
  //--------------------------------------- 
  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    transaction tr;    
    tr = transaction::type_id::create("tr");
    
    tr.wr    = (rw.kind == UVM_WRITE);
    tr.addr  = rw.addr;
    
    if(tr.wr == 1'b1) tr.din = rw.data;
    
    return tr;
  endfunction
 
  //---------------------------------------
  // bus2reg method 
  //--------------------------------------- 
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
 
    rw.kind = tr.wr ? UVM_WRITE : UVM_READ;
    rw.data = tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
 
 
 
 
////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
  
  agent          agent_inst;
  top_reg_block  regmodel;   
  top_adapter    adapter_inst;
  
  `uvm_component_utils(env)
  
  //--------------------------------------- 
  // constructor
  //---------------------------------------
  function new(string name = "env", uvm_component parent);
    super.new(name, parent);
  endfunction : new
 
  //---------------------------------------
  // build_phase - create the components
  //---------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent_inst = agent::type_id::create("agent_inst", this);
    regmodel   = top_reg_block::type_id::create("regmodel", this);
    regmodel.build();
    
    
    adapter_inst = top_adapter::type_id::create("adapter_inst",, get_full_name());
  endfunction 
  
 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    regmodel.default_map.set_sequencer( .sequencer(agent_inst.seqr), .adapter(adapter_inst) );
    regmodel.default_map.set_base_addr(0);        
  endfunction 
 
endclass
 
//////////////////////////////////////////////////////////////////////////////////////////////////
 
 
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
env e;
top_reg_seq trseq;
 
 
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e      = env::type_id::create("env",this);
   trseq  = top_reg_seq::type_id::create("trseq");
  
  // e.set_config_int( "*", "include_coverage", 0 );
endfunction
 
virtual task run_phase(uvm_phase phase);
  
  phase.raise_objection(this);
  
  trseq.regmodel = e.regmodel;
  trseq.start(e.agent_inst.seqr);
  phase.drop_objection(this);
  
  phase.phase_done.set_drain_time(this, 200);
endtask
endclass
 
//////////////////////////////////////////////////////////////
 
 
module tb;
  
    
  top_if tif();
    
  top dut (tif.clk, tif.rst, tif.wr, tif.addr, tif.din, tif.dout);
 
  
  initial begin
   tif.clk <= 0;
  end
 
  always #10 tif.clk = ~tif.clk;
 
  
  
  initial begin
    uvm_config_db#(virtual top_if)::set(null, "*", "tif", tif);
    
    uvm_config_db#(int)::set(null,"*","include_coverage", 0); //to remove include coverage message
 
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```

## Read and Write Transaction
- write writes the specified value into the DUT register

```
import uvm_pkg::*;
`include "uvm_macros.svh"
 
//////////////////transaction class
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
 
       bit [7:0] din;
       bit       wr;
       bit       addr;
       bit       rst;
       bit [7:0] dout;   
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
 
 
endclass
 
///////////////////////////////////////////////////////
////////////////////////driver 
 
class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)
 
  transaction tr;
  virtual top_if tif;
 
  function new(input string path = "driver", uvm_component parent = null);
    super.new(path,parent);
  endfunction
 
  virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
    if(!uvm_config_db#(virtual top_if)::get(this,"","tif",tif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  ///////////////reset DUT at the start
  task reset_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b1;
    tif.wr   <= 1'b0;
    tif.din  <= 8'h00;
    tif.addr <= 1'b0;
    repeat(5)@(posedge tif.clk);
    `uvm_info("DRV", "System Reset", UVM_NONE);
    tif.rst  <= 1'b0;
  endtask
  
  //////////////drive DUT
  
  task drive_dut();
    @(posedge tif.clk);
    tif.rst  <= 1'b0;
    tif.wr   <= tr.wr;
    tif.addr <= tr.addr;
    if(tr.wr == 1'b1)
       begin
           tif.din <= tr.din;
         repeat(2) @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Write -> Wdata : %0d",tif.din), UVM_NONE);
       end
      else
       begin  
          repeat(2) @(posedge tif.clk);
           tr.dout = tif.dout;
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
       end    
  endtask
  
  
  
  ///////////////main task of driver
  
   virtual task run_phase(uvm_phase phase);
      tr = transaction::type_id::create("tr");
     forever begin
        seq_item_port.get_next_item(tr);
        drive_dut();
        seq_item_port.item_done();  
      end
   endtask
 
endclass
 
////////////////////////////////////////////////////////////////////////////////
///////////////////////agent class
 
 
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this); 
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
   d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
////////////////////////////////////////////////////////////////////////////////////////
 
 
 
//////////////////////building reg model
 
////////////////////////
 
 
class temp_reg extends uvm_reg;
  `uvm_object_utils(temp_reg)
   
 
  rand uvm_reg_field temp;
 
  
  function new (string name = "temp_reg");
    super.new(name,8,UVM_NO_COVERAGE); 
  endfunction
 
 
  
  function void build; 
    
 
    temp = uvm_reg_field::type_id::create("temp");   
    // Configure
    temp.configure(  .parent(this), 
                     .size(8), 
                     .lsb_pos(0), 
                     .access("RW"),  
                     .volatile(0), 
                     .reset(0), 
                     .has_reset(1), 
                     .is_rand(1), 
                     .individually_accessible(1)); 
 
    
  endfunction
  
endclass
 
 
//////////////////////////////////////creating reg block
 
 
class top_reg_block extends uvm_reg_block;
  `uvm_object_utils(top_reg_block)
  
 
  rand temp_reg 	temp_reg_inst; 
  
 
  function new (string name = "top_reg_block");
    super.new(name, build_coverage(UVM_NO_COVERAGE));
  endfunction
 
 
  function void build;
    
 
    temp_reg_inst = temp_reg::type_id::create("temp_reg_inst");
    temp_reg_inst.build();
    temp_reg_inst.configure(this);
 
 
    default_map = create_map("default_map", 'h0, 1, UVM_LITTLE_ENDIAN); // name, base, nBytes
    default_map.add_reg(temp_reg_inst	, 'h0, "RW");  // reg, offset, access
    
    
    default_map.set_auto_predict(1);
    
    lock_model();
  endfunction
endclass
 
 
/////////////////////////////////////////////////////////////////////////////////////
 
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [7:0] rdata,rdata_m;
    
    bit [7:0] dout_t;
    
    
    /*
    regmodel.temp_reg_inst.write(status,5'h05);
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write Tx to DUT -> Des : %0d and Mir : %0d ", rdata, rdata_m), UVM_NONE);
    
    regmodel.temp_reg_inst.read(status,dout_t);
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Read Tx from DUT -> Des : %0d and Mir : %0d Data read : %0d", rdata, rdata_m, dout_t), UVM_NONE);
 
    */
    
    
 
    
    
    bit [7:0] din_temp;
    
    
    for(int i = 0; i < 5; i ++) begin
    
    
    din_temp = $urandom_range(5, 20);  
    regmodel.temp_reg_inst.write(status,din_temp);
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write Tx to DUT -> Data Write : %0d", rdata_m), UVM_NONE);
    
    regmodel.temp_reg_inst.read(status,dout_t);
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Read Tx from DUT -> Data read : %0d", dout_t), UVM_NONE);
 
    
    
    
    end
 
    
    
  
  endtask
  
  
endclass
 
////////////////////////////////////////////////////////////////////////
///////////////////////reg adapter
 
class top_adapter extends uvm_reg_adapter;
  `uvm_object_utils (top_adapter)
 
  //---------------------------------------
  // Constructor 
  //--------------------------------------- 
  function new (string name = "top_adapter");
      super.new (name);
   endfunction
  
  //---------------------------------------
  // reg2bus method 
  //--------------------------------------- 
  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    transaction tr;    
    tr = transaction::type_id::create("tr");
    
    tr.wr    = (rw.kind == UVM_WRITE);
    tr.addr  = rw.addr;
    
    if(tr.wr == 1'b1) tr.din = rw.data;
    
    return tr;
  endfunction
 
  //---------------------------------------
  // bus2reg method 
  //--------------------------------------- 
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
 
    rw.kind = tr.wr ? UVM_WRITE : UVM_READ;
    rw.data = tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
 
 
 
 
////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
  
  agent          agent_inst;
  top_reg_block  regmodel;   
  top_adapter    adapter_inst;
  
  `uvm_component_utils(env)
  
  //--------------------------------------- 
  // constructor
  //---------------------------------------
  function new(string name = "env", uvm_component parent);
    super.new(name, parent);
  endfunction : new
 
  //---------------------------------------
  // build_phase - create the components
  //---------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent_inst = agent::type_id::create("agent_inst", this);
    regmodel   = top_reg_block::type_id::create("regmodel", this);
    regmodel.build();
    
    
    adapter_inst = top_adapter::type_id::create("adapter_inst",, get_full_name());
  endfunction 
  
 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    regmodel.default_map.set_sequencer( .sequencer(agent_inst.seqr), .adapter(adapter_inst) );
    regmodel.default_map.set_base_addr(0);        
  endfunction 
 
endclass
 
//////////////////////////////////////////////////////////////////////////////////////////////////
 
 
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
env e;
top_reg_seq trseq;
 
 
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e      = env::type_id::create("env",this);
   trseq  = top_reg_seq::type_id::create("trseq");
  
  // e.set_config_int( "*", "include_coverage", 0 );
endfunction
 
virtual task run_phase(uvm_phase phase);
  
  phase.raise_objection(this);
  
  trseq.regmodel = e.regmodel;
  trseq.start(e.agent_inst.seqr);
  phase.drop_objection(this);
  
  phase.phase_done.set_drain_time(this, 200);
endtask
endclass
 
//////////////////////////////////////////////////////////////
 
 
module tb;
  
    
  top_if tif();
    
  top dut (tif.clk, tif.rst, tif.wr, tif.addr, tif.din, tif.dout);
 
  
  initial begin
   tif.clk <= 0;
  end
 
  always #10 tif.clk = ~tif.clk;
 
  
  
  initial begin
    uvm_config_db#(virtual top_if)::set(null, "*", "tif", tif);
    
    uvm_config_db#(int)::set(null,"*","include_coverage", 0); //to remove include coverage message
 
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```

## Using Randomize
```
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [7:0] rdata;
    
     for(int i = 0; i < 10; i++)
     begin 
     regmodel.temp_reg_inst.randomize();
     regmodel.temp_reg_inst.write(status, regmodel.temp_reg_inst.temp.value);
    `uvm_info("SEQ", $sformatf("Random Value : %0d",regmodel.temp_reg_inst.temp.value), UVM_NONE);
     end
 
 
  endtask
  
  
  
endclass
```

## Understanding Reset Methods
reset methods:
- has_reset
- get_reset
- set_reset
- reset
  
```
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
  
  
  
 
  task body;  
    uvm_status_e   status;
    bit [7:0] rdata,rdata_m;
    bit [7:0] rst_reg;
    
    bit rst_status;
    
   //////Check if register has reset value
    rst_status = regmodel.temp_reg_inst.has_reset();
    `uvm_info("SEQ", $sformatf("Reset Value added : %0b ", rst_status), UVM_NONE);
    
    //////accessing default reset value
    rst_reg = regmodel.temp_reg_inst.get_reset();
    `uvm_info("SEQ", $sformatf("Register Reset Value : %0d ", rst_reg), UVM_NONE);
    
    ////////////////accessing mir and des before rst
    rdata =   regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Before Reset -> Mir : %0d Des : %0d ", rdata_m, rdata), UVM_NONE);
    
    ///////////////mir and des value after rst
     $display("--------------Applying Reset to register model ---------------");
     regmodel.temp_reg_inst.reset();
     rdata =   regmodel.temp_reg_inst.get();
     rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("After Reset -> Mir : %0d Des : %0d ", rdata_m, rdata), UVM_NONE);
    
    /////////////updating rst value
    $display("--------------Updating register reset value and applying Reset ---------------");
   
     regmodel.temp_reg_inst.set_reset(8'hff);
     regmodel.temp_reg_inst.reset();
    
     rdata =   regmodel.temp_reg_inst.get();
     rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("After Reset -> Mir : %0d Des : %0d ", rdata_m, rdata), UVM_NONE);
   
 
    
      
    
  
  endtask
  
  
endclass
```
