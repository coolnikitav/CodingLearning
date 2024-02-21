# Getting Started with Interface

## Adding interface to a simple RTL
```
interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
endinterface

module tb;
  
  add_if aif();
  // add dut (aif.a, aif.b, aif.sum);  // positional mapping
  add dut (.a(aif.a), .b(aif.b), .sum(aif.sum));  // mapping by name
  // mapping by name is used more frequently because as the number of ports grows,
  // positional mapping becomes less reliable
  
  initial begin
    aif.a = 4;
    aif.b = 2;
    #10;
    aif.a = 3;
    #10;
    aif.b = 7;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
  
endmodule
```
## Using blocking operator for interface variables
```
interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

module tb;
  
  add_if aif();
  add dut (.a(aif.a), .b(aif.b), .sum(aif.sum), .clk(aif.clk));  // mapping by name

  initial begin
    aif.clk = 0;
  end
  
  always #10 aif.clk = ~aif.clk;
  
  initial begin
    aif.a = 1;
    aif.b = 5;
    #22;
    aif.a = 3;
    #20;
    aif.a = 4;
    #8;
    aif.a = 5;
    #20;
    aif.a = 6;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
  
endmodule
```
## Using non-blocking operator for interface variables
```
interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

module tb;
  
  add_if aif();
  add dut (.a(aif.a), .b(aif.b), .sum(aif.sum), .clk(aif.clk));  // mapping by name

  initial begin
    aif.clk = 0;
  end
  
  always #10 aif.clk = ~aif.clk;
  
  initial begin
    aif.a <= 1;
    aif.b <= 5;
    repeat(3) @(posedge aif.clk);
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
  
endmodule
```
## Why we prefer LOGIC over WIRE and REG in interface
- Interface with all reg type, we are not allowed to connect variable in interface to the output port of DUT
- Interface with all wire type, we are not allowed to apply stimulus using initial or always

## Adding driver code to interface
```
interface add_if;
  
  logic [3:0] a,b;
  logic [4:0] sum;
  logic clk;
  
endinterface

class driver;
  
  virtual add_if aif;  // virtual means the definition of the interface is defined outside the class
  
  task run();
    forever begin
      @(posedge aif.clk);
      aif.a <= 3;
      aif.b <= 3;
    end
  endtask
  
endclass

module tb;
  
  add_if aif();
  
  add dut (.a(aif.a),.b(aif.b),.sum(aif.sum),.clk(aif.clk));
  
  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
  
  driver drv;
  
  initial begin
    drv = new();
    drv.aif = aif;
    drv.run();
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
  
endmodule
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f7504bad-4442-4740-93f6-827cc862f157)

## Important rules for SV
1) Add constructor to transaction in the custom constructor of generator
   ```
   class generator;
     transaction trans;

     function new(mailbox #(transaction) mbx);
       this.mbx = mbx;
       trans = new;
     endfunction
   endclass
   ```
   signle space for variable means correct randc behavior
2) Send deep copy of transaction object instead of original transaction object
   - Independent object for each iteration
   - Object can be used without worrying about path delay
3) Send deep copy
   - Errors coule be injected with methods/constraints
     
## Injecting error
