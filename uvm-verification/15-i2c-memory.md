# Verification of I2C Memory

## Design Code
```
module i2c_mem
(
input clk, rst, wr,
input [6:0] addr,
input [7:0] din,
output  [7:0] datard,
output reg done
);
 
////////////////////////////
wire sda;
reg scl;
reg [7:0] addrt;
reg [7:0] temprd;
reg en;
reg sdat;
integer count = 0;
 
reg [7:0] mem [128];
integer countn = 0;
reg [7:0] addrn, data_rd, datan;
reg sdan;
reg update;  
  
///////////////////////////////////////
typedef enum bit [3:0] {idle = 0, start = 1, send_addr = 2, get_ack1 = 3, send_data = 4, get_ack2= 5, read_data = 6, complete = 7, get_addr = 8, send_ack1 = 9, get_data = 10, send_ack2 = 11 } state_type;
state_type state, nstate;
 
/////////////////////////////////////
 
always@(posedge clk)
begin
if(rst)
begin
addrt <= 0;
temprd <= 0;
en <= 0;
sdat <= 0;
count <= 0;
end
else begin
case(state) 
idle: begin
en    <= 1'b1;
scl   <= 1'b1;
sdat  <= 1'b1;
state <= start;
count <= 0;
done <= 1'b0;
temprd <= 0;
end
 
start: begin
sdat  <= 1'b0;
addrt <= {addr,wr};
state <= send_addr;
end
 
send_addr: begin
if(count <= 7) begin
sdat <= addrt[count];
count <= count + 1;
end
else
begin
state <= get_ack1;
count <= 0;
en    <= 1'b0;
end 
end
 
get_ack1: begin
 if(sda == 1'b0)
   begin
      if(wr == 1'b1)
        begin
        state <= send_data;
        en    <= 1'b1;
        end
      else if (wr == 1'b0 )
       begin
        state <= read_data;
        en    <= 1'b0;
       end
   end
 else
  state <= get_ack1;
end
 
send_data: begin
if(count <= 7) begin
sdat <= din[count];
count <= count + 1;
end
else
begin
state <= get_ack2;
count <= 0;
en    <= 1'b0;
end 
end
 
get_ack2: begin
if(sda == 1'b0)
  state <= complete;
else
  state <= get_ack2;
end
 
read_data: begin
if(count <= 9) begin
//temprd[count] <= sda;
 temprd[7:0] <= {sda,temprd[7:1]}; 
count <= count + 1;
end
else
begin
state <= complete;
count <= 0;
end 
end
 
complete: begin
if(update) begin
done <= 1'b1;
state <= idle;
end
else
state <= complete;
end
 
default : state <= idle;
endcase
end
 
end
 
/////////////////////////////////////////////////////////////////////////////////////////////////////////////
 
 
 
always@(posedge clk)
begin
 if(rst)
   begin
      for(int i = 0; i< 128; i++)
        begin
         mem[i] <= 0;
        end
        
        addrn  <= 0;
        datan  <= 0;
        update <= 0;
   end
else
  begin
   case(nstate)
    idle: begin
        addrn  <= 0;
        datan  <= 0;
        update <= 0;
        data_rd <= 0;
    
      if(scl && sdat)
        nstate <= start;
      else
        nstate <= idle;
    end   
 
    start: begin
      if(scl && !sdat)
        nstate <= get_addr;
      else
        nstate <= start; 
     end
     
    get_addr: begin 
       if(countn <= 7) begin
        addrn[countn] <= sdat;
        countn <= countn + 1;
        end
        else
        begin
        nstate  <= send_ack1;
        countn <= 0;
        
        if(addrn[0] == 1'b0)
         begin
         data_rd <= mem[addrn[7:1]];
         end
        
        end
     end 
     
    send_ack1:begin 
        sdan <= 1'b0;
        if(addrn[0] == 1'b1 && state == send_data)
          begin 
          nstate <= get_data;
          end
         else if(addrn[0] == 1'b0 && state == read_data)
          nstate <= send_data;
         else
          nstate <= send_ack1;
     end
     
    get_data: begin
        if(countn <= 7) begin
        datan[countn] <= sdat;
        countn <= countn + 1;
        end
        else
        begin
        nstate  <= send_ack2;
        countn <= 0;
        mem[addrn[7:1]] <= datan;
        end
    end
    
    
    send_ack2:begin 
        sdan  <= 1'b0;
        nstate <= complete; 
    end
    
    
    send_data: begin
        if(countn <= 7) begin
        sdan   <= data_rd[countn];
        countn <= countn + 1;
        end
        else
        begin
        nstate  <= complete;
        countn <= 0;
        end
    end
    
    
    complete : begin
       update  <= 1'b1;
       nstate  <= idle; 
    end
    
    
    default: nstate <= idle; 
   endcase
  end
end
////////////////////////////////////////////////////////////////////////
 
assign sda = (en == 1'b1) ? sdat : sdan;
assign datard = temprd;
endmodule
 
 
////////////////////////////////////////////////////////////////////////////////
 
interface i2c_i;
  
  logic clk, rst, wr;
  logic [6:0] addr;
  logic [7:0] din;
  logic  [7:0] datard;
  logic done;
  
      
endinterface
```

## Testbench
```
`include "uvm_macros.svh"
 import uvm_pkg::*;
 
 
//////////////////////////////////////////////////////////
 
typedef enum bit [1:0]   {readd = 0, writed = 1, rstdut = 2} oper_mode;
 
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
  
  oper_mode op;
  logic wr;
  randc logic [6:0] addr;
  rand logic [7:0] din;
  logic [7:0] datard;
  logic done;
         
  constraint addr_c { addr <= 10;}
 
 
  function new(string name = "transaction");
    super.new(name);
  endfunction
 
endclass : transaction
 
 
///////////////////////////////////////////////////////////////////////
 
 
///////////////////write seq
class write_data extends uvm_sequence#(transaction);
  `uvm_object_utils(write_data)
  
  transaction tr;
 
  function new(string name = "write_data");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(15)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = writed;
        `uvm_info("SEQ", $sformatf("MODE : WRITE DIN : %0d ADDR : %0d ", tr.din, tr.addr), UVM_NONE);
        finish_item(tr);
      end
  endtask
  
 
endclass
//////////////////////////////////////////////////////////
 
 
class read_data extends uvm_sequence#(transaction);
  `uvm_object_utils(read_data)
  
  transaction tr;
 
  function new(string name = "read_data");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(15)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = readd;
        `uvm_info("SEQ", $sformatf("MODE : READ ADDR : %0d ", tr.addr), UVM_NONE);
        finish_item(tr);
      end
  endtask
  
 
endclass
/////////////////////////////////////////////////////////////////////
 
class reset_dut extends uvm_sequence#(transaction);
  `uvm_object_utils(reset_dut)
  
  transaction tr;
 
  function new(string name = "reset_dut");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(15)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = rstdut;
        `uvm_info("SEQ", "MODE : RESET", UVM_NONE);
        finish_item(tr);
      end
  endtask
  
 
endclass
////////////////////////////////////////////////////////////
 
 
 
////////////////////////////////////////////////////////////
class driver extends uvm_driver #(transaction);
  `uvm_component_utils(driver)
  
  virtual i2c_i vif;
  transaction tr;
 
  
  function new(input string path = "drv", uvm_component parent = null);
    super.new(path,parent);
  endfunction
  
 virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     tr = transaction::type_id::create("tr");
      
      if(!uvm_config_db#(virtual i2c_i)::get(this,"","vif",vif))//uvm_test_top.env.agent.drv.aif
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  
  
  ////////////////////reset task
  task reset_dut(); 
    begin
    `uvm_info("DRV", "System Reset", UVM_MEDIUM);
    vif.rst       <= 1'b1;  ///active high reset
    vif.addr      <= 0;
    vif.din       <= 0; 
    vif.wr        <= 0;
    @(posedge vif.clk);
    end
  endtask
  
  ///////////////////////write 
  task write_d();
    `uvm_info("DRV", $sformatf("mode : WRITE addr : %0d  din : %0d", tr.addr, tr.din), UVM_NONE);
  vif.rst  <= 1'b0;
  vif.wr   <= 1'b1;
  vif.addr <= tr.addr;
  vif.din  <= tr.din;
  @(posedge vif.done);
   
  endtask 
            
   task read_d();         
  `uvm_info("DRV", $sformatf("mode : READ addr : %0d  din : %0d", tr.addr, tr.din), UVM_NONE);
  vif.rst  <= 1'b0;
  vif.wr   <= 1'b0;
  vif.addr <= tr.addr;
  vif.din  <= 0;
  @(posedge vif.done);        
   endtask
  
  
 
  virtual task run_phase(uvm_phase phase);
    forever begin
     
         seq_item_port.get_next_item(tr);
     
     
                   if(tr.op ==  rstdut)
                          begin
                          reset_dut();
                          end
 
                  else if(tr.op == writed)
                          begin
                          write_d();
                          end
    
                else if(tr.op ==  readd)
                          begin
					      read_d();
                          end
                          
       seq_item_port.item_done();
     
   end
  endtask
 
  
endclass
 
//////////////////////////////////////////////////////////////////////////////////////////////
 
 
class mon extends uvm_monitor;
`uvm_component_utils(mon)
 
uvm_analysis_port#(transaction) send;
transaction tr;
virtual i2c_i vif;
logic [15:0] din;
logic [7:0] dout;
 
    function new(input string inst = "mon", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = transaction::type_id::create("tr");
    send = new("send", this);
      if(!uvm_config_db#(virtual i2c_i)::get(this,"","vif",vif))//uvm_test_top.env.agent.drv.aif
        `uvm_error("MON","Unable to access Interface");
    endfunction
    
    
    virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.clk);
      
      if(vif.rst)
        begin
        tr.op      = rstdut; 
        `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
        send.write(tr);
        end
        
        
      else begin
        
        if(vif.wr)
               begin
                      tr.op = writed;
                      tr.addr = vif.addr;
                      tr.wr   = 1;
                      tr.din  = vif.din;
                      @(posedge vif.done);
                      `uvm_info("MON", $sformatf("DATA WRITE addr:%0d data:%0d",tr.addr,tr.din), UVM_NONE); 
                      send.write(tr);
              end
        else if (!vif.wr)
              begin
                      tr.op = readd; 
                      tr.addr = vif.addr;
                      tr.wr   = 0;
                      tr.din  = vif.din;
                      @(posedge vif.done);  
                      tr.datard = vif.datard;
                      `uvm_info("MON", $sformatf("DATA READ addr:%0d data:%0d ",tr.addr,tr.datard), UVM_NONE); 
                      send.write(tr);
           end      
    end
end
   endtask 
 
endclass
//////////////////////////////////////////////////////////////////////////////////////////////////
 
class sco extends uvm_scoreboard;
`uvm_component_utils(sco)
 
  uvm_analysis_imp#(transaction,sco) recv;
  bit [7:0] arr[128] = '{default:0};
  bit [7:0] data_rd = 0;
 
 
 
    function new(input string inst = "sco", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    recv = new("recv", this);
    endfunction
    
    
  virtual function void write(transaction tr);
    if(tr.op == rstdut)
              begin
                `uvm_info("SCO", "SYSTEM RESET DETECTED", UVM_NONE);
              end  
    else if (tr.op == writed)
      begin
          arr[tr.addr] = tr.din;
          `uvm_info("SCO", $sformatf("DATA WRITE OP  addr:%0d, wdata:%0d arr_wr:%0d",tr.addr,tr.din,  arr[tr.addr]), UVM_NONE);
      end
 
    else if (tr.op == readd)
                begin
                  data_rd = arr[tr.addr];
                  if (data_rd == tr.datard)
                    `uvm_info("SCO", $sformatf("DATA MATCHED : addr:%0d, rdata:%0d",tr.addr,tr.datard), UVM_NONE)
                         else
                     `uvm_info("SCO",$sformatf("TEST FAILED : addr:%0d, rdata:%0d data_rd_arr:%0d",tr.addr,tr.datard,data_rd), UVM_NONE) 
                end
     
  
    $display("----------------------------------------------------------------");
    endfunction
 
endclass
 
 
//////////////////////////////////////////////////////////////////////////////////////////////
                  
 
 
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
 
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 mon m; 
 
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
 
   m = mon::type_id::create("m",this);
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
 
  
  
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
    d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
//////////////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
`uvm_component_utils(env)
 
function new(input string inst = "env", uvm_component c);
super.new(inst,c);
endfunction
 
agent a;
sco s;
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
  a = agent::type_id::create("a",this);
  s = sco::type_id::create("s", this);
endfunction
 
  
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
 a.m.send.connect(s.recv);
endfunction
 
endclass
 
//////////////////////////////////////////////////////////////////////////
 
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
env e;
write_data wdata; 
read_data rdata;
reset_dut rstdut;  
 
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e      = env::type_id::create("env",this);
   wdata  = write_data::type_id::create("wdata");
   rdata  = read_data::type_id::create("rdata");
   rstdut = reset_dut::type_id::create("rstdut");
endfunction
 
virtual task run_phase(uvm_phase phase);
phase.raise_objection(this);
rstdut.start(e.a.seqr);
 
wdata.start(e.a.seqr);
 
rdata.start(e.a.seqr);
 
phase.drop_objection(this);
endtask
endclass
 
//////////////////////////////////////////////////////////////////////
module tb;
  
    
    
  i2c_i vif();
  
  i2c_mem dut (.clk(vif.clk), .rst(vif.rst), .wr(vif.wr), .addr(vif.addr), .din(vif.din), .datard(vif.datard), .done(vif.done));
  
  initial begin
    vif.clk <= 0;
  end
 
  always #10 vif.clk <= ~vif.clk;
 
  
  
  initial begin
    uvm_config_db#(virtual i2c_i)::set(null, "*", "vif", vif);
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
  
endmodule
```
