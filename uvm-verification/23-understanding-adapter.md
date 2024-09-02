# Understanding Adapter

## Usage of Adapter
Needed to transform reg transaction to a bus transaction. Bus transactions have the same data members as the DUT. Reg do not.

![image](https://github.com/user-attachments/assets/6bdd5ae8-6872-44e5-8522-f75f4722cbf5)

## Structure of uvm_reg_bus_op struct
![image](https://github.com/user-attachments/assets/3143965b-f09a-4284-8b28-72efc13c7ec3)

## Complete Flow
![image](https://github.com/user-attachments/assets/1a64f7c8-5110-45e6-ba5b-18db7df5df78)

## Understanding reg2bus
![image](https://github.com/user-attachments/assets/675b9b1b-ad6b-416d-80ac-5b8ca4500f6a)

![image](https://github.com/user-attachments/assets/bf63bca2-b1d3-431a-b176-0e61155ff6c7)

![image](https://github.com/user-attachments/assets/7aaffbf9-6a2a-4a26-9b89-692184b5c969)

## Understanding bus2reg
![image](https://github.com/user-attachments/assets/043cadb7-b0ff-4045-912f-9c76a76a0862)

## Adapter code with native memory ports
```
class top_adapter extends uvm_reg_adapter;
  `uvm_object_utils(top_adapter)
  
  function new(stinr gname = "top_adapter");
    super.new(name);
  endfunction
  
  function uvm_sequence_item reg2bus(const reg uvm_reg_bus_op rw);
    transaction tr;
    tr = transaction::type_id::create("tr");
    
    tr.wr   = (rw.kind == UVM_WRITE) ? 1'b1 : 1'b0;
    tr.addr = rw.addr;
    if(tr.wr == 1'b1) tr.din = rw.data;
    if(tr.wr == 1'b0) tr.dout = rw.data;
    
    return tr;
  endfunction
  
  function uvm_sequence_item bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction tr;
    
    assert($cast(tr, bus_item));
    
    rw.kind = (tr.wr == 1'b1) ? UVM_WRITE : UVM_READ;
    rw.data = tr.dout;
    rw.addr = tr.addr;
    rw.status = UVM_IS_OK;
  endfunction
endclass
```

## Adapter code with protocol specific ports
```
class adapter extends uvm_reg_adapter;
  `uvm_object_utils(adapter)
  
  function new(string name = "adapter");
    super.new(name);
  endfunction
  
  virtual function uvm_sequence_item reg2bus(uvm_reg_bus_op rw);
    apb_item apb = apb_item::type_id::create("apb_tem");
    
    apb.op = (rw.kind == UVM_READ) ? apb::READ : apb::WRITE;
    apb.addr = rw.addr;
    apb.data = rw.data;
    
    return apb;
  endfunction
  
  virtual function void bus2reg(uvm_sequencer_item bus_item, uvm_reg_bus_op rw);
    apb_item apb;
    
    if (!$cast(apb, bus_item)) begin
      `uvm_fatal("CONVERT_APB2REG", "Bus item is not of type apb_item")
    end
    rw.kind = apb.op == apb::READ ? UVM_READ : UVM_WRITE;
    rw.addr = apb.addr;
    rw.data = apb.data;
    rw.status = UVM_IS_OK;
  endfunction
endclass
```

## Summary
![image](https://github.com/user-attachments/assets/c300a058-e944-4d16-851b-9f592aedde5c)

![image](https://github.com/user-attachments/assets/67ea32f1-6246-40c1-b39a-9a63dc28c2ba)
