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

## nexttime
```
module tb;
  reg clk = 0, rst = 0;
  always #5 clk = ~clk;
  
  initial begin
    repeat(5) @(posedge clk);
    rst = 1;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #100;
    $finish();
  end
  
  // We want reset to be true after 5 clock cycles
  A1: assert property (@(posedge clk) s_nexttime[5] rst) $info("success at %0t", $time);
endmodule

# KERNEL: Info: testbench.sv (19): success at 55
# KERNEL: Info: testbench.sv (19): success at 65
# KERNEL: Info: testbench.sv (19): success at 75
# KERNEL: Info: testbench.sv (19): success at 85
# KERNEL: Info: testbench.sv (19): success at 95
# RUNTIME: Info: RUNTIME_0068 testbench.sv (15): $finish called.
# KERNEL: Time: 100 ns,  Iteration: 0,  Instance: /tb,  Process: @INITIAL#10_2@.
# KERNEL: stopped at time: 100 ns
# VSIM: Simulation has finished. There are no more test vectors to simulate.
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion "A1" FAILED at time: 100ns, scope: tb, start-time: 55ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion "A1" FAILED at time: 100ns, scope: tb, start-time: 65ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion "A1" FAILED at time: 100ns, scope: tb, start-time: 75ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion "A1" FAILED at time: 100ns, scope: tb, start-time: 85ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion "A1" FAILED at time: 100ns, scope: tb, start-time: 95ns
```

```
initial A1: assert property (@(posedge clk) s_nexttime[5] rst) $info("success at %0t", $time);

# KERNEL: Info: testbench.sv (19): success at 55
```

## until
- overlapping (until_with) - at least one clock tick with signals sharing behavior
  - until_with
  - s_until_with
- non-overlapping (until)
  - until
  - s_until
 
Example: sig1 should remain true until we have sig2 becoming true
- sig1 s_until sig2

## Demonstration
```
module tb;
  reg clk = 0, rst = 0, ce = 0;
  always #5 clk = ~clk;  
  
  initial begin
    rst = 1;
    #30;
    rst = 1;
    #10;
    ce = 1;
    rst = 1;
    #10;
    rst = 0;
    #50;
    ce = 0;
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;
    $assertvacuousoff(0);
    #100;
    $finish();
  end
  
  initial A1: assert property (@(posedge clk) rst s_until ce) $info("Suc at %0t", $time);
endmodule

# KERNEL: Info: testbench.sv (26): Suc at 45
```

```
module tb;
  reg clk = 0, rst = 0, ce = 0;
  always #5 clk = ~clk;  
  
  initial begin
    rst = 1;
    #30;
    rst = 0;
    #10;
    rst = 1;
    #10;
    ce = 1;
    rst = 0;
    #50;
    ce = 0;
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;
    $assertvacuousoff(0);
    #100;
    $finish();
  end
  
  initial A1: assert property (@(posedge clk) rst s_until ce) $info("Suc at %0t", $time);
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(26): Assertion "A1" FAILED at time: 35ns, scope: tb, start-time: 5ns
```

## Strong and Weak nature of until
```
module tb;
  reg clk = 0, rst = 0, ce = 0;
  always #5 clk = ~clk;  
  
  initial begin
    rst = 1;
    #30;
    rst = 1;
    #10;
    ce = 0;
    rst = 1;
    #10;
    rst = 1;
    #50;
    ce = 0;
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;
    $assertvacuousoff(0);
    #100;
    $finish();
  end
  
  initial A1: assert property (@(posedge clk) rst s_until ce) $info("Suc at %0t", $time);
  initial A2: assert property (@(posedge clk) rst until ce) $info("Suc at %0t", $time);
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(26): Assertion "A1" FAILED at time: 100ns, scope: tb, start-time: 5ns
```

## Followed by Operator
followed by
- implication
  - overlapping (#-#)
  - non-overlapping (#=#)
 
When the antecedent fails, followed by gives a failure instead of a vacuous success.
 
## Demonstration
```
module tb;
  reg clk = 0, rst = 0, ce = 0;
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #20;
    ce = 1;
    rst = 0;
    #20;
    ce = 0;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #50;
    $finish();
  end
  
  initial A1: assert property (@(posedge clk) rst[*2] |-> ##1 ce[*2]) $info("A1 suc at %0t", $time);
  initial A2: assert property (@(posedge clk) rst[*2] |=> ce[*2]) $info("A2 suc at %0t", $time);
  initial A3: assert property (@(posedge clk) rst[*2] #=# ce[*2]) $info("A3 suc at %0t", $time);
  initial A4: assert property (@(posedge clk) rst[*2] #-# ##1 ce[*2]) $info("A4 suc at %0t", $time);
endmodule

# KERNEL: Info: testbench.sv (22): A1 suc at 35
# KERNEL: Info: testbench.sv (23): A2 suc at 35
# KERNEL: Info: testbench.sv (24): A3 suc at 35
# KERNEL: Info: testbench.sv (25): A4 suc at 35
```
