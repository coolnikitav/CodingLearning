# Fundamentals of System Verilog OOP Construct

## Fundamentals of Class

```
class first;
  
  bit [2:0] data0;
  bit [1:0] data1;
  
endclass

module tb;
  
  first f;
  
  f.data0;
  f.data1;
  
endmodule
```
Constructor will allocate the space for the data member and initialize them to the default values of the data type.
```
initial begin
    f = new();  // constructor
  end
```
```
class first;
  
  reg [2:0] data0;
  reg [1:0] data1;
  
endclass

module tb;
  
  first f;  // handler
  
  initial begin
    f = new();  // constructor
    #1;  // wait for everything to settle
    $display("value of data0 : %0d and data1 : %0d",f.data0,f.data1);  // value of data0 : x and data1 : x
  end
  
endmodule
```
```
class first;
  
  reg [2:0] data0;
  reg [1:0] data1;
  
endclass

module tb;
  
  first f;
  
  initial begin
    f = new();
    f.data0 = 3'b010;
    f.data1 = 2'b10;
    #1;
    $display("value of data0 : %0d and data1 : %0d",f.data0,f.data1);
    f = null;  // deallocate the memory
  end
  
endmodule
```

## Ways to add method to class
- task
  - supports timing control: @ (posedge clk)
  - multiple output port
- function
  - does not support timing control
  - single output port
 
### Using function
```
module tb;
  
  function bit [4:0] add (input bit [3:0] a,b);   
    return a + b;   
  endfunction
  
  bit [4:0] res = 0;
  
  initial begin
    res = add(4'b0100,4'b0100);
    $display("res : %0d", res);  // res : 8
  end
  
endmodule
```
```
module tb;
  
  function bit [4:0] add (input bit [3:0] a,b);   
    return a + b;   
  endfunction
  
  bit [4:0] res = 0;
  bit [3:0] ain = 4'b0100;
  bit [3:0] bin = 4'b0010;
  
  initial begin
    res = add(ain,bin);
    $display("res : %0d", res);  // res : 8
  end
  
endmodule
```
```
module tb;
  
  function bit [4:0] add (input bit [3:0] a = 4'b0100,b = 4'b0010);  // default values   
    return a + b;   
  endfunction
  
  bit [4:0] res = 0;
  
  initial begin
    res = add();
    $display("res : %0d", res);  // res : 6
  end
  
endmodule
```
```
module tb;

  // it doesn't matter where in the code the values are declared
  bit [4:0] res = 0;
  bit [3:0] ain = 4'b0100;
  bit [3:0] bin = 4'b0010;
  
  function bit [4:0] add ();
    return ain + bin;   
  endfunction
  
 
  
  initial begin
    res = add();
    $display("res : %0d", res);  // res : 6
  end
  
endmodule
```
```
module tb;
  
  function bit [4:0] add ();
    return ain + bin;   
  endfunction
  
  function void display_ain_bin();
    $display("ain : %0b, bin : %0b", ain, bin);
  endfunction
  
  bit [4:0] res = 0;
  bit [3:0] ain = 4'b0100;
  bit [3:0] bin = 4'b0010;
  
  initial begin
    res = add();
    display_ain_bin();
    $display("res : %0d", res);  // res : 6
  end
  
endmodule
```
Functions 
```
function void display_ain_bin();
    #10;  // error
    $display("ain : %0b, bin : %0b", ain, bin);
  endfunction
```
