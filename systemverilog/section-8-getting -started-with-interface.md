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
