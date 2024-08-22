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
module tb;
  reg clk = 0;
  
  reg rd = 0;
  reg wr = 0;
  reg rst = 0;
  
  reg done = 0;
  
  int delayW, delayR;
  
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #20;
    rst = 0;
  end
  
  task write();
    for (int i = 0; i < 5; i++) begin
      @(negedge clk);
      delayW = $urandom_range(1,3);
      wr = 1;
      @(posedge clk);
      wr = 0;
      repeat(delayW) @(posedge clk);
    end
  endtask
  
  task read();
    for (int i = 0; i < 5; i++) begin
      @(negedge clk);
      delayR = $urandom_range(1,3);
      repeat(delayR) @(posedge clk);
      rd = 1;
      repeat(2) @(posedge clk);
      rd = 0;
    end
  endtask
  
  initial begin
    #20;
    fork
      write();
      read();
    join
  end
  
  initial begin
    #295;
    done = 1;
    #10;
    done = 0;
  end
  
  // consecutive repetition operator
  // rd goes high, stays high for 2 CC, then goes low
  A1: assert property (@(posedge clk) $rose(rd) |-> rd[*2] ##1 !rd) $info("[%0t]: RD high for 2 CC", $time);
    
  // Non-consecutive rep
  // rst goes low, wr has 5 high CC (non-consecutive permitted)
  // rst goes low, 5 non-consecutive rising edge of rd
  A2: assert property (@(posedge clk) $fell(rst) |-> wr[=5]) $info("[%0t]: 5 WR cycles success", $time);
  A3: assert property (@(posedge clk) $fell(rst) |-> $rose(rd)[=5]) $info("[%0t]: 5 RD cycles success", $time);
    
  // Goto operator
  // rst goes low, 5 rising edge of wr, wr stays zero until done is high
  // rst goes low, 5 rising edge of rd, rd stays zero until done is high
  A4: assert property (@(posedge clk) $fell(rst) |-> $rose(wr)[->5] ##1 !wr[*1:$] ##1 $rose(done)) $info("[%0t]: WR zero after 5 cycles", $time);
  A5: assert property (@(posedge clk) $fell(rst) |-> $rose(rd)[->5] ##2 !rd[*1:$] ##1 $rose(done)) $info("[%0t]: RD zero after 5 cycles", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #310;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (59): [65]: RD high for 2 CC
# KERNEL: Info: testbench.sv (59): [105]: RD high for 2 CC
# KERNEL: Info: testbench.sv (64): [135]: 5 WR cycles success
# KERNEL: Info: testbench.sv (59): [145]: RD high for 2 CC
# KERNEL: Info: testbench.sv (59): [195]: RD high for 2 CC
# KERNEL: Info: testbench.sv (65): [215]: 5 RD cycles success
# KERNEL: Info: testbench.sv (59): [235]: RD high for 2 CC
# KERNEL: Info: testbench.sv (70): [305]: WR zero after 5 cycles
# KERNEL: Info: testbench.sv (71): [305]: RD zero after 5 cycles
```

## Non-Consecutive Repetition Operator with constant count
```
module tb;
 reg clk = 0;
 
 reg a = 0;
 reg b = 0;
 reg c = 0;
 
 reg temp = 0;
 
 
 always #5 clk = ~clk;
 
 initial begin
   #15;
   a = 1;
   #10;
   a = 0;
 end
 
 initial begin
   temp = 1;
   #185;
   temp = 0;
 end
 
 initial begin
   #20;
   b = 1;
   repeat(2) @(posedge clk); 
   b = 0; 
 end
 
 initial begin
   #94;
   c = 1;
   #10;
   c = 0;
 end
  
 // Need strong, otherwise it will not print failure during failure because its waiting for the 3 instances
 A1: assert property (@(posedge clk) $rose(a) |-> strong(b[=3])) $info("Non-con suc @ %0t", $time);
 A2: assert property (@(posedge clk) $rose(a) |-> strong(b[->3])) $info("GOTO suc @ %0t", $time);
    
 initial begin 
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0);
   #200;
   $finish();
 end
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(41): Assertion "A1" FAILED at time: 200ns, scope: tb, start-time: 25ns
# ASSERT: Error: ASRT_0005 testbench.sv(42): Assertion "A2" FAILED at time: 200ns, scope: tb, start-time: 25ns
```

## Non-Consecutive Repetition Operator with Range
```
module tb;
 reg clk = 0;
 
 reg a = 0;
 reg b = 0;
 reg c = 0;
 
 reg temp = 0;
 
 
 always #5 clk = ~clk;
 
 initial begin
   #15;
   a = 1;
   #10;
   a = 0;
 end
 
 initial begin
   temp = 1;
   #185;
   temp = 0;
 end
 
 initial begin
   #20;
   b = 1;
   repeat(3) @(posedge clk); 
   b = 0; 
 end
 
 initial begin
   #94;
   c = 1;
   #10;
   c = 0;
 end
  
 // Need strong, otherwise it will not print failure during failure because its waiting for the 3 instances
 A1: assert property (@(posedge clk) $rose(a) |-> strong(b[=3:5])) $info("Non-con suc @ %0t", $time);
 A2: assert property (@(posedge clk) $rose(a) |-> strong(b[->3:5])) $info("GOTO suc @ %0t", $time);
    
 initial begin 
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0);
   #200;
   $finish();
 end
endmodule

# KERNEL: Info: testbench.sv (41): Non-con suc @ 45
# KERNEL: Info: testbench.sv (42): GOTO suc @ 45
```

## Summary
- repetition operator
  - consecutive [*]
    - pass - no. of repetition = or > repetition count of operator
    - fail - no. of repetition < repetition count
    - to restrict specific count: add tail expression: a[*3] ##1 !a
  - repetition with range [*x:y] min:max
    - pass - no. of repetition = min count specified
    - fail - no. of repetition < min specified count
    - fail - if tail expression do not hold within the max specified count a[*1:3] ##1 !a
  - non-consecutive [=]
    - pass - no. of repetition = specified count
    - fail + strong (rep. must occur) - no. of repetition < specified count
    - fail + tail expression (restrict repetition) - tail expression hold after repetition
  - range
    - pass - rep count = min count
    - fail - fail count < min count
    - fail + tail expression - tail expression do not hold after max rep count reached

## GOTO vs Non-consecutive Insights
- a[->2] = !a[*0:$] ##1 a ##1 !a[*0:$] ##1 a (sequence ends)
- a[=2] = !a[*0:$] ##1 a ##1 !a[*0:$] ##1 a (match) ##!a[*0:$]

- a[->3] ##1 a; // ##1 a must happen immediately after the a[->3] sequence for a match
- a[=3] ##1 a; // ##1 there can be delay after after a[=3]

```
module tb;
   reg clk = 0;
 
   reg a = 0;
   reg b = 0;

   always #5 clk = ~clk;

   initial begin
     #15;
     a = 1;
     #10;
     a = 0;
   end

   initial begin
     #20;
     b = 1;
     repeat(3) @(posedge clk); 
     b = 0; 
     #50;
     b = 1;
     #10;
     b = 0;
   end

   A1: assert property (@(posedge clk) $rose(a) |-> b[=3] ##1 b) $info("Non-con suc @ %0t", $time);
   A2: assert property (@(posedge clk) $rose(a) |-> b[->3] ##1 b) $info("GOTO suc @ %0t", $time);
    
   initial begin 
     $dumpfile("dump.vcd");
     $dumpvars;
     $assertvacuousoff(0);
     #150;
     $finish();
   end
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(28): Assertion "A2" FAILED at time: 55ns, scope: tb, start-time: 25ns
# KERNEL: Info: testbench.sv (27): Non-con suc @ 105
```

## Use Cases
- Write request must be followed by read request. If read do not assert before timeout then system should reset
  - (!rst[*1:$] ##1 timeout) |-> rst;
- Write request must be followed by read request
  - $rose(wr) |-> ##1 $rose(rd);
- If a assert, b must assert in 5 CC
  - $rose(a) |-> ##5 $rose(b);
- If rst deassert then CE must assert within 1 to 3 CC
  - $fell(rst) |-> ##[1:3] $rose(CE);
- If req assert and ack not received in the 3 CC then req must reassert
  - $rose(req) ##1 !ack[*3] |-> $rose(req);
- If a assert, a must remain high for 3 CC
  - $rose(a) |-> a[*3];
- System operation must start with rst asserted for 3 consecutive CC
  - initial A1: assert property(@(posedge clk) rst[*3]);
- CE must assert somewhere during simulation if reset deasserts
  - $fell(rst) |-> ##[1:$] $rose(CE);
- Transaction start with CE become high and ends with CE become low. Each transaction must contain at least one read and write request.
  - $rose(CE) |-> (rd[->1] && wr[->1]) ##1 !CE;
- If CE assert somewhere after rst deassert then we must received at least one write request
  - $fell(rst) ##[1:$] $rose(CE) |-> wr[->1];
- a must assert twice during simulation
  - a[=2];
- If a becomes high somewhere then b must become high in the immediate next clock tick
  - $rose(a) |=> $rose(b);
- If req is received and all the data is sent to slave indicated by done signal then ready must be high in the next CC
  - $rose(req) ##1 done[->1] |-> ##1 ready;
