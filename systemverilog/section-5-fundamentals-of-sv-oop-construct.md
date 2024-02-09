# Fundamentals of SystemVerilog OOP Construct

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
Functions cannot contain time-controlled statements
```
function void display_ain_bin();
    #10;  // error
    $display("ain : %0b, bin : %0b", ain, bin);
  endfunction
```
### Using function
```
module tb;
  
  // default direction : input
  task add (input bit [3:0] a, input bit [3:0] b, output bit [4:0] y);
    y = a + b;
  endtask
  
  bit [3:0] a,b;
  bit [4:0] y;
  
  initial begin
    a = 7;
    b = 7;
    add(a,b,y);
    $display("value of y : %0d", y);  // value of y : 14
  end
  
endmodule
```
```
module tb;
  
  // default direction : input
  /*
  task add (input bit [3:0] a, input bit [3:0] b, output bit [4:0] y);
    y = a + b;
  endtask
  */
  
  bit [3:0] a,b;
  bit [4:0] y;
  
  task add ();
    y = a + b;
  endtask
  
  initial begin
    a = 7;
    b = 7;
    add();
    $display("value of y : %0d", y);  // value of y : 14
  end
  
endmodule
```
```
module tb;
  
  bit [3:0] a,b;
  bit [4:0] y;
  
  task add ();
    y = a + b;
    $display("a : %0d, b : %0d, value of y : %0d", a,b,y);
  endtask
  
  task stim_a_b();
    a = 1;
    b = 3;
    add();  // a : 1, b : 3, value of y : 4
    #10;
    a = 5;
    b = 6;
    add();  // a : 5, b : 6, value of y : 11
    #10;
    a = 7;
    b = 8;
    add();  // a : 7, b : 8, value of y : 15
    #10;
  endtask
  
  initial begin
    stim_a_b();    
  end
  
endmodule
```
```
module tb;
  
  bit [3:0] a,b;
  bit [4:0] y;
  
  bit clk = 0;
  
  always #10 clk = ~clk;  // 20 ns --> 50 MHz
  
  task add ();
    y = a + b;
    $display("a : %0d, b : %0d, value of y : %0d", a,b,y);
  endtask
  
  task stim_a_b();
    a = 1;
    b = 3;
    add();  // a : 1, b : 3, value of y : 4
    #10;
    a = 5;
    b = 6;
    add();  // a : 5, b : 6, value of y : 11
    #10;
    a = 7;
    b = 8;
    add();  // a : 7, b : 8, value of y : 15
    #10;
  endtask
  
  task stim_clk();
    @(posedge clk); // wait
    a = $urandom();  
    b = $urandom();
    add();
  endtask
  
  initial begin
    #110;
    $finish;
  end
  
  initial begin
    // stim_a_b();
    
    for (int i = 0; i < 11; i++) begin
      stim_clk();
    end
  end
  
endmodule
```
