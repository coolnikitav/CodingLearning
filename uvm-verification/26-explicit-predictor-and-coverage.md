# Explicit Predictor and Coverage

## Understanding Design for Explicit Predictor
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
    //@(posedge tif.clk);
    tif.rst  <= 1'b0;
    tif.wr   <= tr.wr;
    tif.addr <= tr.addr;
    if(tr.wr == 1'b1)
       begin
          tif.din <= tr.din;
         `uvm_info("DRV", $sformatf("Data Write -> Wdata : %0d",tr.din), UVM_NONE);
          repeat(3) @(posedge tif.clk);
             end
      else
       begin  
         repeat(2) @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
           tr.dout = tif.dout;
         @(posedge tif.clk);
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
 
/////////////////////////////////////monitor 
 
      
class monitor extends uvm_monitor;
    `uvm_component_utils( monitor )
 
    uvm_analysis_port   #(transaction)  mon_ap;
    virtual     top_if              tif;
    transaction tr;
    
    function new(string name="my_monitor", uvm_component parent);
        super.new(name, parent);
    endfunction : new
  
    virtual function void build_phase(uvm_phase phase);
        super.build_phase (phase);
        mon_ap = new("mon_ap", this);
      if(! uvm_config_db#(virtual top_if)::get (this, "", "tif", tif))
        `uvm_error("MON", "Error getting Interface Handle")
    endfunction : build_phase
  
    virtual task run_phase(uvm_phase phase);
     tr = transaction::type_id::create("tr");
            forever begin
              repeat(3) @(posedge tif.clk);
                  tr.wr    = tif.wr;
                  tr.addr  = tif.addr;
                  tr.din   = tif.din;
                  tr.dout  = tif.dout;
                  `uvm_info("MON", $sformatf("Wr :%0b  Addr : %0d Din:%0d  Dout:%0d", tr.wr, tr.addr, tr.din, tr.dout), UVM_NONE)         
                  mon_ap.write(tr);
               
                end 
    endtask 
 
      
endclass
      
/////////////////////////////////////scoreboard
      
 class sco extends uvm_scoreboard;
`uvm_component_utils(sco)
 
  uvm_analysis_imp#(transaction,sco) recv;
   bit [7:0] temp_data;
  bit [31:0] temp;
 
 
    function new(input string inst = "sco", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    recv = new("recv", this);
    endfunction
    
    
  virtual function void write(transaction tr);
    `uvm_info("SCO", $sformatf("Wr :%0b  Addr : %0d Din:%0d  Dout:%0d", tr.wr, tr.addr, tr.din, tr.dout), UVM_NONE) 
 
    if(tr.wr == 1'b1)
        begin
          if(tr.addr == 1'b0) 
            begin
             temp_data = tr.din;
            `uvm_info("SCO", $sformatf("Data Stored : %0d", tr.din), UVM_NONE) 
            end
          else
            begin
              `uvm_info("SCO", "No Such Addr", UVM_NONE)
            end
        end
    else
       begin
          if(tr.addr == 1'b0) 
            begin
              if(tr.dout == temp_data)
                `uvm_info("SCO", "Test Passed", UVM_NONE) 
            end
          else
            begin
              `uvm_info("SCO", "No Such Addr", UVM_NONE);
            end
        end
    
    
        
  endfunction
 
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
 monitor m;
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   d = driver::type_id::create("d",this);
   m = monitor::type_id::create("m",this);
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
 
  
  
  
///////////////user defined build function
  
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
    bit [7:0] data;
    bit [7:0] read_d;
    bit [7:0] des, mir;
    
    
    
    for (int i = 0; i < 5; i++) begin
     data = $urandom;
     regmodel.temp_reg_inst.write(status, data);
     des = regmodel.temp_reg_inst.get();
     mir = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write -> Des: %0d Mir: %0d", des, mir), UVM_NONE);
  
      
     regmodel.temp_reg_inst.read(status, read_d);
     des = regmodel.temp_reg_inst.get();
     mir = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Read -> Des: %0d Mir: %0d", des, mir), UVM_NONE);
  
     $display("---------------------------------------------------------------------------"); 
      
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
 
    rw.kind = (tr.wr == 1'b1) ? UVM_WRITE : UVM_READ;
    rw.data = (tr.wr == 1'b1) ? tr.din : tr.dout;///rw.data = tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
 
 
 
 
 
 
 
////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
 `uvm_component_utils(env)
  
  agent          agent_inst;
  top_reg_block  regmodel;   
  top_adapter    adapter_inst;
  uvm_reg_predictor   #(transaction)  predictor_inst;
  
  sco s;
  
  
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
    predictor_inst = uvm_reg_predictor#(transaction)::type_id::create("predictor_inst", this);
    agent_inst = agent::type_id::create("agent_inst", this);
    s = sco::type_id::create("s", this);
    regmodel   = top_reg_block::type_id::create("regmodel", this);
    regmodel.build();
    
    
    adapter_inst = top_adapter::type_id::create("adapter_inst",, get_full_name());
    
 
  endfunction 
  
 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    agent_inst.m.mon_ap.connect(s.recv);
     
    regmodel.default_map.set_sequencer( .sequencer(agent_inst.seqr), .adapter(adapter_inst) );
    regmodel.default_map.set_base_addr(0);
    
    
    
    predictor_inst.map       = regmodel.default_map;
    predictor_inst.adapter   = adapter_inst;
    agent_inst.m.mon_ap.connect(predictor_inst.bus_in);
   
    
    regmodel.default_map.set_auto_predict(0);
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
  
  trseq.regmodel = e.regmodel;
  trseq.start(e.agent_inst.seqr);
  phase.drop_objection(this);
  
  phase.phase_done.set_drain_time(this, 20);
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

## Coverage Analysis
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
    //@(posedge tif.clk);
    tif.rst  <= 1'b0;
    tif.wr   <= tr.wr;
    tif.addr <= tr.addr;
    if(tr.wr == 1'b1)
       begin
          tif.din <= tr.din;
         `uvm_info("DRV", $sformatf("Data Write -> Wdata : %0d",tr.din), UVM_NONE);
          repeat(3) @(posedge tif.clk);
             end
      else
       begin  
         repeat(2) @(posedge tif.clk);
          `uvm_info("DRV", $sformatf("Data Read -> Rdata : %0d",tif.dout), UVM_NONE);
           tr.dout = tif.dout;
         @(posedge tif.clk);
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
 
/////////////////////////////////////monitor 
 
      
class monitor extends uvm_monitor;
    `uvm_component_utils( monitor )
 
    uvm_analysis_port   #(transaction)  mon_ap;
    virtual     top_if              tif;
    transaction tr;
    
    function new(string name="my_monitor", uvm_component parent);
        super.new(name, parent);
    endfunction : new
  
    virtual function void build_phase(uvm_phase phase);
        super.build_phase (phase);
        mon_ap = new("mon_ap", this);
      if(! uvm_config_db#(virtual top_if)::get (this, "", "tif", tif))
        `uvm_error("MON", "Error getting Interface Handle")
    endfunction : build_phase
  
    virtual task run_phase(uvm_phase phase);
     tr = transaction::type_id::create("tr");
            forever begin
              repeat(3) @(posedge tif.clk);
                  tr.wr    = tif.wr;
                  tr.addr  = tif.addr;
                  tr.din   = tif.din;
                  tr.dout  = tif.dout;
                  `uvm_info("MON", $sformatf("Wr :%0b  Addr : %0d Din:%0d  Dout:%0d", tr.wr, tr.addr, tr.din, tr.dout), UVM_NONE)         
                  mon_ap.write(tr);
               
                end 
    endtask 
 
      
endclass
      
/////////////////////////////////////scoreboard
      
 class sco extends uvm_scoreboard;
`uvm_component_utils(sco)
 
  uvm_analysis_imp#(transaction,sco) recv;
   bit [7:0] temp_data;
  bit [31:0] temp;
 
 
    function new(input string inst = "sco", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    recv = new("recv", this);
    endfunction
    
    
  virtual function void write(transaction tr);
    `uvm_info("SCO", $sformatf("Wr :%0b  Addr : %0d Din:%0d  Dout:%0d", tr.wr, tr.addr, tr.din, tr.dout), UVM_NONE) 
 
    if(tr.wr == 1'b1)
        begin
          if(tr.addr == 1'b0) 
            begin
             temp_data = tr.din;
            `uvm_info("SCO", $sformatf("Data Stored : %0d", tr.din), UVM_NONE) 
            end
          else
            begin
              `uvm_info("SCO", "No Such Addr", UVM_NONE)
            end
        end
    else
       begin
          if(tr.addr == 1'b0) 
            begin
              if(tr.dout == temp_data)
                `uvm_info("SCO", "Test Passed", UVM_NONE) 
            end
          else
            begin
              `uvm_info("SCO", "No Such Addr", UVM_NONE);
            end
        end
    
    
        
  endfunction
 
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
 monitor m;
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   d = driver::type_id::create("d",this);
   m = monitor::type_id::create("m",this);
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
 
////////////////////////adding coverpoints     
  
 covergroup temp_cov;
    
   option.per_instance = 1;
    
    
   coverpoint temp.value[7:0] 
    {
      bins lower = {[0:63]};
      bins mid = {[64:127]};
      bins high = {[128:255]};
    }
     
  endgroup
 
  ////////////////checking coverage and adding new method to covergroup
  
  function new (string name = "temp_reg");
    super.new(name,8,UVM_CVR_FIELD_VALS);
    
    if(has_coverage(UVM_CVR_FIELD_VALS))
      temp_cov = new();
    
  endfunction
 
//////////////////////////////   implementation of sample and sample_Values  
  
  
  virtual function void sample(uvm_reg_data_t data,
                                uvm_reg_data_t byte_en,
                                bit            is_read,
                                uvm_reg_map    map);
    
         temp_cov.sample();
   endfunction
  
  
  
   virtual function void sample_values();
    super.sample_values();
     
    temp_cov.sample();
     
  endfunction
  
  
  
  
  
///////////////user defined build function
  
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
    
    uvm_reg::include_coverage("*", UVM_CVR_ALL);
 
    temp_reg_inst = temp_reg::type_id::create("temp_reg_inst");
    temp_reg_inst.build();
    temp_reg_inst.configure(this);
    temp_reg_inst.set_coverage(UVM_CVR_FIELD_VALS); //////enabling coverage for specific reg instance       
 
 
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
    bit [7:0] data;
    bit [7:0] read_d;
    bit [7:0] des, mir;
    
    
    
    for (int i = 0; i < 5; i++) begin
     data = $urandom;
     regmodel.temp_reg_inst.write(status, data);
     des = regmodel.temp_reg_inst.get();
     mir = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write -> Des: %0d Mir: %0d", des, mir), UVM_NONE);
  
      
     regmodel.temp_reg_inst.read(status, read_d);
     des = regmodel.temp_reg_inst.get();
     mir = regmodel.temp_reg_inst.get_mirrored_value();
    `uvm_info("SEQ", $sformatf("Write -> Des: %0d Mir: %0d", des, mir), UVM_NONE);
  
     $display("---------------------------------------------------------------------------"); 
      
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
 
    rw.kind = (tr.wr == 1'b1) ? UVM_WRITE : UVM_READ;
    rw.data = (tr.wr == 1'b1) ? tr.din : tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
 
 
 
 
 
 
 
////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
 `uvm_component_utils(env)
  
  agent          agent_inst;
  top_reg_block  regmodel;   
  top_adapter    adapter_inst;
  uvm_reg_predictor   #(transaction)  predictor_inst;
  
  sco s;
  
  
  
 
  
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
    predictor_inst = uvm_reg_predictor#(transaction)::type_id::create("predictor_inst", this);
    agent_inst = agent::type_id::create("agent_inst", this);
    s = sco::type_id::create("s", this);
    regmodel   = top_reg_block::type_id::create("regmodel", this);
    regmodel.build();
    
    
    adapter_inst = top_adapter::type_id::create("adapter_inst",, get_full_name());
    
 
  endfunction 
  
 
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    agent_inst.m.mon_ap.connect(s.recv);
     
    regmodel.default_map.set_sequencer( .sequencer(agent_inst.seqr), .adapter(adapter_inst) );
    regmodel.default_map.set_base_addr(0);
    
    
    
    predictor_inst.map       = regmodel.default_map;
    predictor_inst.adapter   = adapter_inst;
    agent_inst.m.mon_ap.connect(predictor_inst.bus_in);
   
    
    regmodel.default_map.set_auto_predict(0);
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
  
  trseq.regmodel = e.regmodel;
  trseq.start(e.agent_inst.seqr);
  phase.drop_objection(this);
  
  phase.phase_done.set_drain_time(this, 20);
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
