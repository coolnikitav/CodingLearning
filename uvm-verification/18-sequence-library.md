# Understanding usage of Sequence Library

```
import uvm_pkg::*;
`include "uvm_macros.svh"

class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)

  rand bit [3:0] a;
  rand bit [3:0] b;

  function new (string name = "transaction");
    super.new(name);
  endfunction
endclass

typedef class seq_library;

class seq1 extends uvm_sequence#(transaction);
  `uvm_object_utils(seq1)

  transaction tr;

  function new (string name = "seq1");
    super.new(name)
  endfunction

  virtual task body();
    tr = transaction::type_id::create("tr");
    start_item(tr);
    tr.a = 4;
    tr.b = 4;
    finish_item(tr);
  endtask
endclass

class seq2 extends uvm_sequence#(transaction);
  `uvm_object_utils(seq2)

  transaction tr;

  function new (string name = "seq2");
    super.new(name)
  endfunction

  virtual task body();
    tr = transaction::type_id::create("tr");
    start_item(tr);
    tr.a = 5;
    tr.b = 5;
    finish_item(tr);
  endtask
endclass

class seq_library extends uvm_sequence_library#(transaction);
  `uvm_object_utils(seq_library)
  `uvm_sequence_library_utils(seq_library)

  function new (string name = "seq_library");'
    super.new(name);
    // If you have added instance of sequence in sequence library, use seq_name.get_type (dot operator)
    // If not, use seq_name::get_tyep() (scope operator)
    add_typewide_sequence(seq1::get_type());
    add_typewide_sequence(seq2::get_type());
  endfunction
endclass

class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)

  transaction tr;

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(tr);
      `uvm_info(get_type_name(), $sformatf("a: %0d b: %0d", tr.a, tr.b), UVM_NONE);
      #10;
      seq_item_port.item_done();
    end
  endtask
endclass

class agent extends uvm_agent;
  `uvm_component_utils(agent)

  function new (input string inst = "agent", uvm_component parent = null);
    super.new(inst, parent);
  endfunction

  driver d;
  uvm_sequencer#(transaction) seqr;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    d = driver::type_id::create("d", this);
    seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
  endfunction

  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    d.seq_item_port.connect(seqr.seq_item_export);
  endfunction
endclass

class env extends uvm_env;
  `uvm_component_utils(env)

  function new (input string inst = "env", uvm_component c);
    super.new(inst, c);
  endfunction

  agent a;

  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    a = agent::type_id::create("a", this);
  endfunction
endclass

class test extends uvm_test;
  `uvm_component_utils(test)

  env e;
  seq_library seqlib;

  function new (input string inst = "test", uvm_component c);
    super.new(inst, c):
  endfunction

  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    e = env::type_id::create("e", this);
    seqlib = seq_library::type_id::create("seqlib", this);
    seqlib.selection_mode = UVM_SEQ_LIB_RANDC;
    seqlib.min_random_count = 5;   // min number of sequences to execute
    seqlib.max_random_count = 10;  // max number of sequences to execute
    seqlib.init_sequence_library();
    seqlib.print();
  endfunction

  virtual task run_phase (uvm_phase phase);
    phase.raise_objection(this);
    assert(seqlib.randomize());
    seqlib.start(e.a.seqr);
    phase.drop_objection(this);
  endtask
endclass

module top();
  initial begin
    run_test("test");
  end
endmodule
```
