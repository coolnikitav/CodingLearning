# Linear Temporal Logic Operators

## Getting Started with "eventually"
- eventually - checking if the condition ever occurs during the simulation. It is a weak property. A range needs to be specified
- s-eventually - same as eventually, but a strong property. The can be called with or without a range

## Common Usage of "eventually"
- CE assert eventually
- rst must go down withon 3 to 10 clock ticks
- CE assert eventually and stay high
- rst deassert eventually and stay low

## Demonstration of "eventually"
```
module tb;
  reg clk = 0, rst = 1,  ce = 0;
  
  always #5 clk = ~clk;  
  
  initial begin
    rst = 1;
    #40;
    rst = 0;
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;
    $assertvacuousoff(0);
    #120;
    $finish();
  end 
 
  // reset must eventually become low and stay low until the end of the simulation
  initial A1: assert property(@(posedge clk) s_eventually always !rst) $info("suc at %0t", $time);
endmodule

# KERNEL: Info: testbench.sv (21): suc at 120
```

```
initial A1: assert property(@(posedge clk) eventually[3:10] !rst) $info("suc at %0t", $time);

# KERNEL: Info: testbench.sv (22): suc at 45
```

## Strong and Weak Demonstration
