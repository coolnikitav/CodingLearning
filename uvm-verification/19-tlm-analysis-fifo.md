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
