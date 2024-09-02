# Adding Register and Memory to Verification Environment

## Advantage of UVM RAL
- Abstraction
  
![image](https://github.com/user-attachments/assets/17728040-7063-4e29-852e-773395e86ed3)

Downside of the 2 methods above is that we need to keep track of all of the registers and it becomes messy.

Using RAL:
```
class ctrl_wr extends uvm_sequence;

  `uvm_object_utils(ctrl_wr)

  reg_block regmodel;
  uvm_reg_data_t ref_data;

  function new(string name = "ctrl_wr");
    super.new(name);
  endfunction

  task body;
    uvm_status_e status;
    bit [3:0] rdata;
    bit [3:0] wdata;
    bit [7:0] rdatad, rdata_m;

    for (int i = 0; i < 5; i++) begin
      wdata = $urandom();
      regmodel.cntrl_inst.write(status, wdata);
    end
  endtask
endclass
```

- Flexibility

![image](https://github.com/user-attachments/assets/77dd829d-6776-43bd-9b05-a9b5a08577ba)

- Built in methods to compare state of registers'

![image](https://github.com/user-attachments/assets/cc874d9b-178d-499e-952c-12333d313643)

- Support coverage computation + in-depth analysis

![image](https://github.com/user-attachments/assets/12759e99-c148-42b1-87dd-941ba48a753e)

![image](https://github.com/user-attachments/assets/e8c79854-038f-42a9-9c2c-a2a0ba2d8bf1)

## When to use RAL in Verification Environment
- Q: What are the requirements?

Min. requirements:
- At least single register/memory exist in DUT
- Register have at least a single field
- Registers are address mapped

Example:
```
// This does not meet the third requirement

module top (
  input clk, write,
  input [31:0] data_in,
  output reg [31:0] data_out,
  output done
);
  reg [31:0] temp;/// [31:16] --> addr  [15:0] --> data

  always@(posedge clk)
    begin
      if(write)
         temp <= data_in;
      else
         data_out <= temp;
    end 
endmodule
```

Good example:
```
module top (
  input clk, write,addr,
  input [31:0] data_in,
  output reg [31:0] data_out,
  output done
);
  reg [31:0] temp;

  always@(posedge clk) begin
    if(write) begin
      if(addr == 0) begin
        temp <= data_in;
      end
    end else begin
      if(addr == 0) begin
        data_out <= temp;
      end
    end
  end  
endmodule
```

## Components of Register Model
![image](https://github.com/user-attachments/assets/26102f9d-7ec9-470e-abfe-885c331e26a4)

![image](https://github.com/user-attachments/assets/bc331f33-2661-44e9-acb2-185922c2c9ca)

## Understanding Different Types of Registers
![image](https://github.com/user-attachments/assets/7d773dbd-c6f3-4882-a4c1-d64f31c61005)

## Implementation of Register in Verification Environment
1 Register with a single reg field:
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class reg0 extends uvm_reg;
  `uvm_object_utils(reg0)
  
  rand uvm_reg_field slv_reg0;
  
  function new(string name = "reg0");
    super.new(name,32,UVM_NO_COVERAGE);
  endfunction
  
  function void build;
    slv_reg0 = uvm_reg_field::type_id::create("slv_reg0");
    
    // Configure
    slv_reg0.configure(
      .parent(this),
      .size(32),
      .lsb_pos(0),
      .access("RW"),
      .volatile(0),
      .reset('h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(1)
    );
  endfunction
endclass

module tb;
  reg0 r0;
  
  initial begin
    r0 = new("r0");
    r0.build();
  end
endmodule
```
## Configure Function
![image](https://github.com/user-attachments/assets/02de5e74-9213-48ca-8856-7afc624c011f)

![image](https://github.com/user-attachments/assets/705c2c7c-d7a0-4e40-bdf1-7b8584ad3750)

## Adding Register with Two Fields
```
`include "uvm_macros.svh"
import uvm_pkg::*;

class reg2 extends uvm_reg;
  `uvm_object_utils(reg2)
  
  rand uvm_reg_field slv_cntrl;
  rand uvm_reg_field slv_data;
  
  function new(string name = "reg2");
    super.new(name,32,UVM_NO_COVERAGE);
  endfunction
  
  function void build;
    slv_cntrl = uvm_reg_field::type_id::create("slv_cntrl");
    slv_cntrl.configure(
      .parent(this),
      .size(16),
      .lsb_pos(0),
      .access("RW"),
      .volatile(0),
      .reset(16'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(1)
    );
    
    slv_data = uvm_reg_field::type_id::create("slv_data");
    slv_data.configure(
      .parent(this),
      .size(16),
      .lsb_pos(16),
      .access("RW"),
      .volatile(0),
      .reset(16'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(1)
    );
  endfunction
endclass

module tb;
  reg2 r2;
  
  initial begin
    r2 = new("r2");
    r2.build();
  end
endmodule
```

## Adding Register with Reserved Bits
![image](https://github.com/user-attachments/assets/eb7918e3-0c03-4ab4-8aa4-1536bdf9f8bf)

```
`include "uvm_macros.svh"
import uvm_pkg::*;

class reg3 extends uvm_reg;
  `uvm_object_utils(reg3)
  
  rand uvm_reg_field en;
  rand uvm_reg_field mode;
  rand uvm_reg_field addr;
  rand uvm_reg_field data;
  
  function new(string name = "reg3");
    super.new(name,32,UVM_NO_COVERAGE);
  endfunction
  
  function void build;
    en = uvm_reg_field::type_id::create("en");
    en.configure(this,1,0,"RW",0,0,1,1,0);
    
    mode = uvm_reg_field::type_id::create("mode");
    mode.configure(this,3,1,"RW",0,0,1,1,0);
    
    addr = uvm_reg_field::type_id::create("addr");
    addr.configure(this,8,4,"RW",0,0,1,1,0);
    
    data = uvm_reg_field::type_id::create("data");
    data.configure(this,16,12,"RW",0,0,1,1,0);
  endfunction
endclass

module tb;
  reg3 r3;
  
  initial begin
    r3 = new("r3");
    r3.build();
  end
endmodule
```

## Different Access Policy
![image](https://github.com/user-attachments/assets/ba59fe5e-3520-4fce-80e1-6c26e3e804aa)

![image](https://github.com/user-attachments/assets/15e9cd78-558c-4712-8e91-8680d30230be)

![image](https://github.com/user-attachments/assets/a6137cc9-b881-47f9-b68d-b585fb475bd6)

![image](https://github.com/user-attachments/assets/9d1927db-9c1e-408f-aa24-9d95b2a69775)

![image](https://github.com/user-attachments/assets/0f796f96-bb03-484c-abad-11d49db98435)

![image](https://github.com/user-attachments/assets/1de4b0bc-e89d-4cb1-8d73-b9949912a5d8)

![image](https://github.com/user-attachments/assets/7bf86ab3-7c03-499d-8b7b-82d8711af42a)

![image](https://github.com/user-attachments/assets/8e8fd8a4-c7c1-4dbe-aafd-f3f61878c61a)

![image](https://github.com/user-attachments/assets/fca3e065-889c-4dfa-9285-dc7591b6a485)

![image](https://github.com/user-attachments/assets/e98bb2f5-3ade-449a-b375-5c7cc98d0cf1)

![image](https://github.com/user-attachments/assets/0ff75280-34d7-4a95-8b1b-8768a6be99ad)

![image](https://github.com/user-attachments/assets/b1b84f8e-9bdc-4d65-adb5-90df8e4f0419)
