# Different Ways of Accessing Register and Memories

## Type of Access Methods
![image](https://github.com/user-attachments/assets/d1f30263-a876-4b26-9205-bf34136ee3a5)

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
    
    
    
    regmodel.temp_reg_inst.write(status,5'h05, UVM_FRONTDOOR);
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write Tx to DUT -> Des : %0d and Mir : %0d ", rdata, rdata_m), UVM_NONE);
    
    regmodel.temp_reg_inst.read(status,dout_t, UVM_FRONTDOOR);
    rdata = regmodel.temp_reg_inst.get();
    rdata_m = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Read Tx from DUT -> Des : %0d and Mir : %0d Data read : %0d", rdata, rdata_m, dout_t), UVM_NONE);
 
    
    
  
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

## Fundamentals of Backdoor Access
![image](https://github.com/user-attachments/assets/577dd995-b3d4-4063-8a6c-f695332af742)

![image](https://github.com/user-attachments/assets/a63f4c3c-55ae-4247-ac47-9dbfa42484e0)

![image](https://github.com/user-attachments/assets/6a436e4b-1b11-4d2b-9c32-6909d6a9265b)

![image](https://github.com/user-attachments/assets/7d9188ec-8f39-4c59-8586-739675c12ce0)

```
import uvm_pkg::*;
`include "uvm_macros.svh"
 
//////////////////transaction class
 
class transaction extends uvm_sequence_item;
 
       bit [3:0] din;
       bit       wr;
       bit       addr;
       bit       rst;
       bit [3:0] dout;   
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
  
 
  `uvm_object_utils_begin(transaction)
    `uvm_field_int(din,UVM_ALL_ON)
    `uvm_field_int(wr,UVM_ALL_ON)
    `uvm_field_int(addr,UVM_ALL_ON)
    `uvm_field_int(dout,UVM_ALL_ON)
  `uvm_object_utils_end
  
 
 
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
    tif.wr   <= 1'b1;
  //  tif.din  <= 4'b0000;
    tif.addr <= 1'b0;
    repeat(5)@(posedge tif.clk);
    `uvm_info("DRV", $sformatf("SYSTEM RESET Wdata : %0d", tif.din), UVM_NONE);
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
         repeat(2)  @(posedge tif.clk);
         tr.dout = tif.dout;
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
       end    
  endtask
  
  
  //
  ///////////////main task of driver
  
   virtual task run_phase(uvm_phase phase);
 //    reset_dut();   ///////reset at start of simulation
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
    super.new(name,4,UVM_NO_COVERAGE); 
  endfunction
 
 
  
  function void build; 
    
 
    temp = uvm_reg_field::type_id::create("temp");   
    // Configure
    temp.configure(  .parent(this), 
                     .size(4), 
                     .lsb_pos(0), 
                     .access("RW"),  
                   .volatile(0), 
                     .reset(2), 
                     .has_reset(1), 
                     .is_rand(1), 
                   .individually_accessible(0)); 
    // Below line is equivalen to above one   
    // temp.configure(this, 32,       0,   "RW",   0,        0,        1,        1,      0); 
    //                  reg, bitwidth, lsb, access, volatile, reselVal, hasReset, isRand, fieldAccess
    
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
    
    add_hdl_path ("dut", "RTL");
 
    temp_reg_inst = temp_reg::type_id::create("temp_reg_inst");
    temp_reg_inst.build();
    temp_reg_inst.configure(this,null);
    temp_reg_inst.add_hdl_path_slice("tempin",0, 4); //reg name in rtl,starting position,no.of bits wide
    
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN,0); // name, base, nBytes
    default_map.add_reg(temp_reg_inst	, 'h0, "RW");  // reg, offset, access
    default_map.set_auto_predict(1);
    
    
    lock_model();
  endfunction
endclass
 
 
/////////////////////////////////////////////////////////////////////////////////////
 
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
   uvm_reg_data_t ref_data;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [3:0] rdata;
    
    
    ///////frontdoor write
    regmodel.temp_reg_inst.write(status, 4'hf, UVM_FRONTDOOR);
     ref_data = regmodel.temp_reg_inst.get(); ///get the desired value
    `uvm_info("REG_SEQ", $sformatf("Desired Value backdoor: %0d", ref_data), UVM_NONE);
    ref_data = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("REG_SEQ", $sformatf("Mirror Value backdoor: %0d", ref_data), UVM_NONE);
    
  
    
    ////////////////backdoor read
    regmodel.temp_reg_inst.read(status, rdata, UVM_BACKDOOR);
    `uvm_info("REG_SEQ",$sformatf("Backdoor read",rdata),UVM_LOW);
    
    
    ///////////////////backdoor write
    
    regmodel.temp_reg_inst.write(status, 4'he, UVM_BACKDOOR);
     ref_data = regmodel.temp_reg_inst.get(); ///get the desired value
    `uvm_info("REG_SEQ", $sformatf("Desired Value backdoor: %0d", ref_data), UVM_NONE);
    ref_data = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("REG_SEQ", $sformatf("Mirror Value backdoor: %0d", ref_data), UVM_NONE);
 
    
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
    
    tr.wr    = (rw.kind == UVM_WRITE) ? 1'b1 : 1'b0;
    tr.addr  = rw.addr;
    if(tr.wr == 1'b1) tr.din  = rw.data;
    if(tr.wr == 1'b0) tr.dout = rw.data;
    
    return tr;
  endfunction
 
  //---------------------------------------
  // bus2reg method 
  //--------------------------------------- 
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
 
    rw.kind = (tr.wr == 1'b1) ? UVM_WRITE : UVM_READ;
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
endfunction
 
virtual task run_phase(uvm_phase phase);
  phase.raise_objection(this);
  assert(trseq.randomize());
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
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```
```
import uvm_pkg::*;
`include "uvm_macros.svh"
 
//////////////////transaction class
 
class transaction extends uvm_sequence_item;
 
       bit [3:0] din;
       bit       wr;
       bit       addr;
       bit       rst;
       bit [3:0] dout;   
  
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
  
 
  `uvm_object_utils_begin(transaction)
    `uvm_field_int(din,UVM_ALL_ON)
    `uvm_field_int(wr,UVM_ALL_ON)
    `uvm_field_int(addr,UVM_ALL_ON)
    `uvm_field_int(dout,UVM_ALL_ON)
  `uvm_object_utils_end
  
 
 
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
    tif.wr   <= 1'b1;
  //  tif.din  <= 4'b0000;
    tif.addr <= 1'b0;
    repeat(5)@(posedge tif.clk);
    `uvm_info("DRV", $sformatf("SYSTEM RESET Wdata : %0d", tif.din), UVM_NONE);
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
         repeat(2)  @(posedge tif.clk);
         tr.dout = tif.dout;
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
       end    
  endtask
  
  
  //
  ///////////////main task of driver
  
   virtual task run_phase(uvm_phase phase);
 //    reset_dut();   ///////reset at start of simulation
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
    super.new(name,4,UVM_NO_COVERAGE); 
  endfunction
 
 
  
  function void build; 
    
 
    temp = uvm_reg_field::type_id::create("temp");   
    // Configure
    temp.configure(  .parent(this), 
                     .size(4), 
                     .lsb_pos(0), 
                   .access("RO"),  
                   .volatile(0), 
                     .reset(2), 
                     .has_reset(1), 
                     .is_rand(1), 
                   .individually_accessible(0)); 
    // Below line is equivalen to above one   
    // temp.configure(this, 32,       0,   "RW",   0,        0,        1,        1,      0); 
    //                  reg, bitwidth, lsb, access, volatile, reselVal, hasReset, isRand, fieldAccess
    
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
    temp_reg_inst.configure(this,null);
    temp_reg_inst.add_hdl_path_slice("tempin",0, 4); //reg name in rtl,starting position,no.of bits wide
 
 
    default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN,0); // name, base, nBytes
    default_map.add_reg(temp_reg_inst	, 'h0, "RW");  // reg, offset, access
    default_map.set_auto_predict();
    
    add_hdl_path ("dut", "RTL");
    lock_model();
  endfunction
endclass
 
 
/////////////////////////////////////////////////////////////////////////////////////
 
class top_reg_seq extends uvm_sequence;
 
  `uvm_object_utils(top_reg_seq)
  
   top_reg_block regmodel;
   uvm_reg_data_t ref_data;
  
   
  function new (string name = "top_reg_seq"); 
    super.new(name);    
  endfunction
  
 
  task body;  
    uvm_status_e   status;
    bit [3:0] rdata;
    bit [3:0] des, mir;
    
     regmodel.temp_reg_inst.poke(status, 4'hf);
     des = regmodel.temp_reg_inst.get();
     mir = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write -> Des: %0d Mir: %0d", des, mir), UVM_NONE);
    $display("-----------------------------------------------");
    regmodel.temp_reg_inst.peek(status, rdata);
    `uvm_info(get_type_name(),$sformatf("READ : %0d",rdata),UVM_LOW);
     des = regmodel.temp_reg_inst.get();
     mir = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Des: %0d Mir: %0d", des, mir), UVM_NONE);
     
    
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
    
    tr.wr    = (rw.kind == UVM_WRITE) ? 1'b1 : 1'b0;
    tr.addr  = rw.addr;
    if(tr.wr == 1'b1) tr.din  = rw.data;
    if(tr.wr == 1'b0) tr.dout = rw.data;
    
    return tr;
  endfunction
 
  //---------------------------------------
  // bus2reg method 
  //--------------------------------------- 
  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
 
    rw.kind = (tr.wr == 1'b1) ? UVM_WRITE : UVM_READ;
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
endfunction
 
virtual task run_phase(uvm_phase phase);
  phase.raise_objection(this);
  assert(trseq.randomize());
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
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```
