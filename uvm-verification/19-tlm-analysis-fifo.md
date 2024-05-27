# Understanding TLM Analysis FIFO

## Understanding usage

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e70c80a3-552e-49c3-93e1-92bfb654927c)

## Demonstration
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class sender extends uvm_component;
  `uvm_component_utils(sender)

  logic [3:0] data;

  uvm_blocking_put_port#(logic [3:0]) send;

  function new(input string path = "sender", uvm_component parent = null);
    super.new(path, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase)
    send = new("send", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      for (int i = 0; i < 5; i++) begin
        data = $random;
        `uvm_info("sender", $sformatf("Data: %0d iteration: %0d", data, i), UVM_NONE);
        send.put(data);
        #20;
      end
    end
  endtask 
endclass

class receiver extends uvm_component;
  `uvm_component_utils(receiver)

  logic [3:0] datar;

  uvm_blocking_put_port#(logic [3:0]) recv;

  function new(input string path = "receiver", uvm_component parent = null);
    super.new(path, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase)
    recv = new("recv", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      for (int i = 0; i < 5; i++) begin
        #40;
        recv.get(datar);
        `uvm_info("receiver", $sformatf("Data: %0d iteration: %0d", datar, i), UVM_NONE);
      end
    end
  endtask 
endclass

class test extends uvm_test;
  `uvm_component_utils(test)

  uvm_tlm_fifo#(logic [3:0]) fifo;

  sender s;
  receiver r;

  function new (input string path = "test", uvm_component parent = null);
    super.new(path, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    fifo = new("fifo", this, 10);  // third parameter is depth, set it to 0 to store any number of transactions
    s = sender::type_id::create("s", this);
    r = receiver::type_id::create("r", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    s.send.connect(fifo.put_export);
    r.recv.connect(fifo.get_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    #200;  // 40*5
    phase.drop_objection(this);
  endtask
endclass

module tb;
  initial begin
    run_test("test");
  end
endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5478bb03-2d1b-4aa9-8b86-b90f8eaaf0e8)

## Design
```
module mux(
input [3:0] a,b,c,d,
input [1:0] sel,
output reg [3:0] y
);
   
always@(*)
    begin
     case(sel)
      2'b00 : y = a;
      2'b01 : y = b;
      2'b10 : y = c;
      2'b11 : y = d;
      default : y = 4'b0000;
     endcase
    end
 
endmodule
 
 
 
interface mux_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] c;
  logic [3:0] d;
  logic [1:0] sel;
  logic [3:0] y;
endinterface
```

## Verification
```
`include "uvm_macros.svh"
import uvm_pkg::*;
 
////////////////////////////////////////////////////////////
class transaction extends uvm_sequence_item;
  
  
   rand bit [3:0] a;
   rand bit [3:0] b;
   rand bit [3:0] c;
   rand bit [3:0] d;
   rand bit [1:0] sel;
        bit [3:0] y;
        
   function new(input string path = "transaction");
    super.new(path);
   endfunction
  
  `uvm_object_utils_begin(transaction)
  `uvm_field_int(a, UVM_DEFAULT)
  `uvm_field_int(b, UVM_DEFAULT)
  `uvm_field_int(c, UVM_DEFAULT)
  `uvm_field_int(d, UVM_DEFAULT)
  `uvm_field_int(sel, UVM_DEFAULT)
  `uvm_field_int(y, UVM_DEFAULT)
  `uvm_object_utils_end
  
 
endclass
 
////////////////////////////////////////////////////////////////////////
 
class generator extends uvm_sequence#(transaction);
`uvm_object_utils(generator)
  
    transaction tr;
 
   function new(input string path = "generator");
    super.new(path);
   endfunction
   
   
   virtual task body(); 
   repeat(15)
     begin
     tr = transaction::type_id::create("tr");
     start_item(tr);
     assert(tr.randomize());
     `uvm_info("SEQ", $sformatf("a:%0d  b:%0d c:%0d d:%0d sel:%0d y:%0d", tr.a, tr.b,tr.c,tr.d,tr.sel,tr.y), UVM_NONE);
     finish_item(tr);     
     end
   endtask
 
endclass
//////////////////////////////////////////////////////////////////////////////
class drv extends uvm_driver#(transaction);
  `uvm_component_utils(drv)
 
  transaction tr;
  virtual mux_if mif;
 
  function new(input string path = "drv", uvm_component parent = null);
    super.new(path,parent);
  endfunction
 
  virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
    if(!uvm_config_db#(virtual mux_if)::get(this,"","mif",mif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
   virtual task run_phase(uvm_phase phase);
      tr = transaction::type_id::create("tr");
     forever begin
        seq_item_port.get_next_item(tr);
        mif.a   <= tr.a;
        mif.b   <= tr.b;
        mif.c   <= tr.c;
        mif.d   <= tr.d;
        mif.sel <= tr.sel;
      `uvm_info("DRV", $sformatf("a:%0d  b:%0d c:%0d d:%0d sel:%0d y:%0d", tr.a, tr.b,tr.c,tr.d,tr.sel,tr.y), UVM_NONE);
       seq_item_port.item_done();
        #20;   
      end
   endtask
 
endclass
 
//////////////////////////////////////////////////////////////////////////
class mon extends uvm_monitor;
`uvm_component_utils(mon)
 
uvm_analysis_port#(transaction) send;
transaction tr;
virtual mux_if mif;
 
    function new(input string inst = "mon", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = transaction::type_id::create("tr");
    send = new("send", this);
    if(!uvm_config_db#(virtual mux_if)::get(this,"","mif",mif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
    endfunction
    
    
    virtual task run_phase(uvm_phase phase);
    forever begin
    #20;
    tr.a   = mif.a;
    tr.b   = mif.b;
    tr.c   = mif.c;
    tr.d   = mif.d;
    tr.sel = mif.sel;
    tr.y   = mif.y;
      `uvm_info("MON_DUT", $sformatf("a:%0d  b:%0d c:%0d d:%0d sel:%0d y:%0d", tr.a, tr.b,tr.c,tr.d,tr.sel,tr.y), UVM_NONE);
     send.write(tr);
    end
   endtask 
 
endclass
 
/////////////////////////////////////////////////////////////////////////
//////////////////////reference model
 
class ref_model extends uvm_monitor;
`uvm_component_utils(ref_model)
 
uvm_analysis_port#(transaction) send_ref;
transaction tr;
virtual mux_if mif;
 
    function new(input string inst = "ref_model", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = transaction::type_id::create("tr");
    send_ref = new("send_ref", this);
    if(!uvm_config_db#(virtual mux_if)::get(this,"","mif",mif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("ref_model","Unable to access Interface");
    endfunction
    
    function void predict();
      case(tr.sel)
       2'b00 : tr.y = tr.a;
       2'b01 : tr.y = tr.b;
       2'b10 : tr.y = tr.c;
       2'b11 : tr.y = tr.d;      
      endcase
    endfunction
    
    virtual task run_phase(uvm_phase phase);
    forever begin
    #20;
    tr.a   = mif.a;
    tr.b   = mif.b;
    tr.c   = mif.c;
    tr.d   = mif.d;
    tr.sel = mif.sel;
    predict();
      `uvm_info("MON_REF", $sformatf("a:%0d  b:%0d c:%0d d:%0d sel:%0d y:%0d", tr.a, tr.b,tr.c,tr.d,tr.sel,tr.y), UVM_NONE);  
    send_ref.write(tr);
    end
   endtask 
 
endclass
 
////////////////////////////////////////////////////////////////////////////
class sco extends uvm_scoreboard;
`uvm_component_utils(sco)
 
 
 
  transaction tr, trref;
 
  
  uvm_tlm_analysis_fifo#(transaction) sco_data;
  uvm_tlm_analysis_fifo#(transaction) sco_data_ref;
  
  
 
 
    function new(input string inst = "sco", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr    = transaction::type_id::create("tr");
    trref = transaction::type_id::create("tr_ref");
    sco_data = new("sco_data", this);
    sco_data_ref = new("sco_data_ref", this);  
      
    endfunction
    
 
  
  
     virtual task run_phase(uvm_phase phase); 
       forever begin
         sco_data.get(tr);
         sco_data_ref.get(trref);
 
         
         if(tr.compare(trref))
         `uvm_info("SCO", "Test Passed", UVM_NONE)
         else
         `uvm_info("SCO", "Test Failed", UVM_NONE)
     
      end
     endtask
     
 
endclass
 
///////////////////////////////////////////////////////////////////////////
 
class agent extends uvm_agent;
`uvm_component_utils(agent)
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
  
 
 drv d;
 uvm_sequencer#(transaction) seqr;
 mon m;
 ref_model mref;
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
 d    = drv::type_id::create("d",this);
 m    = mon::type_id::create("m",this);
 mref = ref_model::type_id::create("mref",this); 
 seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
///////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
`uvm_component_utils(env)
 
function new(input string inst = "env", uvm_component c);
super.new(inst,c);
endfunction
 
agent a;
sco s;
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
  a = agent::type_id::create("agent",this);
  s = sco::type_id::create("sco", this);
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
  a.m.send.connect(s.sco_data.analysis_export);
  a.mref.send_ref.connect(s.sco_data_ref.analysis_export);
endfunction
 
endclass
 
 
//////////////////////////////////////////////////////////////////
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
env e;
generator gen;
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
  e   = env::type_id::create("env",this);
  gen = generator::type_id::create("gen");
endfunction
 
virtual task run_phase(uvm_phase phase);
phase.raise_objection(this);
gen.start(e.a.seqr);
 #20;
phase.drop_objection(this);
endtask
endclass
 
 
////////////////////////////////////////////////////////////////////
module tb;
 
  mux_if mif();
  
  mux dut (.a(mif.a), .b(mif.b), .c(mif.c), .d(mif.d), .sel(mif.sel), .y(mif.y));
 
initial 
  begin
  uvm_config_db #(virtual mux_if)::set(null, "*", "mif", mif);
  run_test("test"); 
  end
 
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule
 
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/bb4f5f9b-2aeb-459f-ae79-b04ece6caf74)
