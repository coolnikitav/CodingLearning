# Sequence Operators

## Getting Started with delay Operator ##
Delay operator types:
- constant (##3): if req becomes high, ack must also become high after 3 tickes
- variable (##[3:5]): when req becomes high, ack must also become high within 3 to 5 ticks
- unbounded (##[:$]): if req becomes high, ack must also become high somewhere during the simulation

## Constant Delay
```
module tb;
 
 reg clk = 0;
 
 reg req = 0;
 reg ack = 0;
 
 always #5 clk = ~clk;
 
 initial begin
   repeat(3) begin
     #1;
     req = 1;
     #5;
     req = 0;
     repeat(3) @(negedge clk);
   end
 end
 
 initial begin
   for(int i = 0; i < 2; i++) begin
     repeat(3) @(posedge clk);
     ack = $urandom_range(0,1);
     @(posedge clk);
     ack = 0;
   end
 end
 
  A1: assert property (@(posedge clk) $rose(req) |-> ##3 $rose(ack)) $info("Suc at %0t", $time); else $error("Failure @ %0t", $time);
    
 initial begin 
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0);
   #100;
   $finish();
 end
endmodule

# KERNEL: Info: testbench.sv (29): Suc at 35
# KERNEL: Error: testbench.sv (29): Failure @ 65
# KERNEL: Error: testbench.sv (29): Failure @ 95
```

## Variable Delay
```
module tb;
  reg clk = 0;
  reg req = 0;
  reg ack = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    repeat(3) begin
      #1;
      req = 1;
      #5;
      req = 0;
      repeat(3) @(negedge clk);
    end
  end
  
  initial begin
    #27;
    ack = 1;
    #5;
    ack = 0;
    #14;
    ack = 1;
    #5;
    ack = 0;
    #60;
    ack = 1;
    #5;
    ack = 0;
  end
  
  A1: assert property (@(posedge clk) $rose(req) |-> ##[2:5] $rose(ack)) $info("Suc @ %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #140;
    $finish();
  end
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(33): Assertion "A1" FAILED at time: 55ns, scope: tb, start-time: 5ns
# ASSERT: Error: ASRT_0005 testbench.sv(33): Assertion "A1" FAILED at time: 85ns, scope: tb, start-time: 35ns
# KERNEL: Info: testbench.sv (33): Suc @ 115
```

## Unbounded Delay
```
module tb;
  reg clk = 0;
  reg req = 0;
  reg ack = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    #2;
    req = 1;
    #5;
    req = 0;
  end
  
  initial begin
    #120;
    ack = 1;
    #10;
    ack = 0;
  end
  
  A1: assert property (@(posedge clk) $rose(req) |-> ##[0:$] $rose(ack)) $info("Suc @ %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #140;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (22): Suc @ 125
```

```
initial begin
    #120;
    ack = 0;
    #10;
    ack = 0;
  end
  
  A1: assert property (@(posedge clk) $rose(req) |-> ##[0:$] $rose(ack)) $info("Suc @ %0t", $time);

// No failure printed
```

- Strong property: need to complete before simulation ends. Unfinished attempts are considered failure at end of simulation
- Weak property: weak property do not need to finish

Unbounded delay is a weak property.

To make it strong:
```
A1: assert property (@(posedge clk) $rose(req) |-> strong(##[1:$] $rose(ack))) $info("Suc @ %0t", $time);

# ASSERT: Error: ASRT_0005 testbench.sv(22): Assertion "A1" FAILED at time: 140ns, scope: tb, start-time: 5ns
```

- ##[*] = ##[0:$]
- ##[+] = ##[1:$]

## Repetition Operator
- Consecutive (*)
- Non-consecutive (=) + Goto (->)

## Consecutive Repetition Operator with Constant Count
```
// 3 consecutive
A1: assert property (@(posedge clk) $rose(rd) |-> rd[*3]) $info("Con rep Suc @ %0t", $time);
```

## Consectuve Repetition Operator with Range
```
A1: assert property (@(posedge clk) $rose(a) |-> b[*2:4]) $info("Suc @ %0t", $time);
```

## Demonstration
```
module tb;
  reg clk = 0;
  reg req1 = 0;
  reg req2 = 0;
  
  int delay1 = 0, delay2 = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 4; i++) begin
      delay1 = $urandom_range(4,8);
      #delay1;
      req1 = 1;
      #20;
      req1 = 0;
      #30;
    end
  end
  
  initial begin
    for (int i = 0; i < 4; i++) begin
      delay2 = $urandom_range(3,5);
      #delay2;
      req2 = 1;
      repeat(delay2) #10;
      req2 = 0;
      #20;
    end
  end
  
  // if req1 asserts, then it should remain stable for 2 clock ticks
  A1: assert property (@(posedge clk) $rose(req1) |-> req1[*2]) $info("req1 rep suc @ %0t", $time);
    
  // if req2 asserts, then it should remain stable for 3 to 5 clock ticks
  A2: assert property (@(posedge clk) $rose(req2) |-> req2[*3:5]) $info("req2 rep suc @ %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #250;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (33): req1 rep suc @ 15
# KERNEL: Info: testbench.sv (36): req2 rep suc @ 25
# KERNEL: Info: testbench.sv (33): req1 rep suc @ 75
# KERNEL: Info: testbench.sv (36): req2 rep suc @ 95
# KERNEL: Info: testbench.sv (33): req1 rep suc @ 125
# KERNEL: Info: testbench.sv (36): req2 rep suc @ 155
# KERNEL: Info: testbench.sv (33): req1 rep suc @ 185
# KERNEL: Info: testbench.sv (36): req2 rep suc @ 225
```

## Consecutive Repetition Operator with Unbounded Range
```
// psel should stay high for at least a cycle and then go low when penable falls
A1: assert property (@(posedge clk) $rose(psel) |-> psel[*1:$] ##1 $fell(penable)) $info("Suc @ %0t", $time);
```

## Use Cases
Check system behavior during the write operation by performing at least five write cycles when reset is disabled
```
assert property (@(posedge clk) $fell(rst) |-> wr[*5:$]);
```

Check system behavior during the read operation by performing at least five read cycles when reset is disabled
```
assert property (@(posedge clk) $fell(rst) |-> rd[*5:$]);
```

During the reading operation, rd signal must remain high for two clock ticks
```
assert property (@(posedge clk) $rose(rd) |-> rd[*2]);
```

Both rd and wr should remain low after completion of five write and read transactions
```
assert property (@(posedge clk) (wr[*5] && rd[*5]) |-> (!rd[*0:$] && !wr[*0:$]));
```
