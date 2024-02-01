# Procedural Constructs

## Types of signals in testbenches
- Global signal (clk, rst)
- Data signal (rdata,wdata)
- Control signal (raddr,waddr,WR,OE)

## Initial block
Starts execution at time 0 (as soon as simulation starts).

```
`timescale 1ns/1ps

module tb;

  reg a = 0;

  // single statement
  initial a = 1;

  // multiple statements
  initial begin
    a = 1;
    #10;
    a = 0;
  end
  
endmodule
```

```
`timescale 1ns/1ps

module tb();

  // global signal clk,rst
  
  reg clk,rst;
  
  reg [3:0] temp;
  
  // 1.Initialize global variables
  initial begin
  	clk = 1'b0;
    rst = 1'b0;
  end
  
  // 2.Random signal for data/control
  initial begin
    rst = 1'b1;
    #30;
    rst = 1'b0;
  end
  
  initial begin
    temp = 4'b0100;
    #10;
    temp = 4'b1100;
    #10;
    temp = 4'b0011;
    #10;
  end
  
  // 3.System task at the start of simulation
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
  
  // 4.Analyzing values of variables on console
  initial begin
    $monitor("Temp : %0d at time : %0t", temp, $time);
  end
  
  // 5.Stop simulation by forecfully calling finish.
  initial begin
    #200;
    $finish();
  end
  
endmodule
```
