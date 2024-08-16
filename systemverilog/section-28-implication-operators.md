# Implication Operators

## Implication Operators Fundamentals
![image](https://github.com/user-attachments/assets/4dc45516-4e51-4bc5-af75-eaa7ae344c11)

![image](https://github.com/user-attachments/assets/9162bd13-6ca8-48f4-8882-919bed68e7b8)

![image](https://github.com/user-attachments/assets/d77c6050-c88f-4116-962a-0a9963f02703)

![image](https://github.com/user-attachments/assets/ccf1ea93-464d-41c7-9eba-98aad320731c)

![image](https://github.com/user-attachments/assets/639da571-c963-4af9-8b81-db3eae2f4fc3)

![image](https://github.com/user-attachments/assets/8d8feaf5-ad0a-49ab-bde2-a218174adfdc)

```
module tb;
  reg clk = 0;
  reg req = 0;
  reg ack = 0;
  
  task req_stimuli();
    #10;
    req = 1;
    #10;
    req = 0;
    #10;
    req = 1;
    #10;
    req = 0;
    #10;
    req = 1;
    #10;
    req = 0;
  endtask
  
  task ack_stimuli();
    #10;
    ack = 1;
    #10;
    ack = 0;
    #10;
    ack = 0;
    #10;
    ack = 0;
    #10;
    ack = 0;
    #10;
  endtask
  
  initial begin
    fork
      req_stimuli();
      ack_stimuli();
    join
  end
  
  always #5 clk = ~clk;
  
  A1: assert property (@(posedge clk) req |-> ack) $info("Overlapping Suc at %0t", $time); else $error("Overlapping Failure at %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (44): Overlapping Suc at 5
# KERNEL: Info: testbench.sv (44): Overlapping Suc at 15
# KERNEL: Info: testbench.sv (44): Overlapping Suc at 25
# KERNEL: Error: testbench.sv (44): Overlapping Failure at 35
# KERNEL: Info: testbench.sv (44): Overlapping Suc at 45
# KERNEL: Error: testbench.sv (44): Overlapping Failure at 55
# KERNEL: Info: testbench.sv (44): Overlapping Suc at 65
# RUNTIME: Info: RUNTIME_0068 testbench.sv (50): $finish called.
```

## Filtering Vacuous Success
```
initial begin
  $dumpfile("dump.vcd");
  $dumpvars;
  $assertvacuousoff(0);
  #60;
  $finish();
end

# KERNEL: Info: testbench.sv (44): Overlapping Suc at 15
# KERNEL: Error: testbench.sv (44): Overlapping Failure at 35
# KERNEL: Error: testbench.sv (44): Overlapping Failure at 55
# RUNTIME: Info: RUNTIME_0068 testbench.sv (51): $finish called.
```

## Non-Overlapping Implication Operator
![image](https://github.com/user-attachments/assets/d771d653-0c04-4340-91a7-e3f388298fd4)

```
module tb;
  reg clk = 0;
  reg req = 0;
  reg ack = 0;
  
  task req_stimuli();
    #10;
    req = 1;
    #10;
    req = 0;
    #10;
    req = 1;
    #10;
    req = 0;
    #10;
    req = 1;
    #10;
    req = 0;
  endtask
  
  task ack_stimuli();
    #10;
    ack = 1;
    #10;
    ack = 1;
    #10;
    ack = 0;
    #10;
    ack = 1;
    #10;
    ack = 0;
    #10;
  endtask
  
  initial begin
    fork
      req_stimuli();
      ack_stimuli();
    join
  end
  
  always #5 clk = ~clk;
  
  A1: assert property (@(posedge clk) req |=> ack) $info("Suc at %0t", $time); else $error("Failure at %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #80;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (44): Suc at 25
# KERNEL: Info: testbench.sv (44): Suc at 45
# KERNEL: Error: testbench.sv (44): Failure at 65
```

## Property and Sequence with Arguments
```
module tb;
  reg ce = 0;
  reg wr = 0;
  reg rd = 0;
  reg clk = 0;
  reg rst = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #30;
    rst = 0;    
  end
  
  initial begin
  	ce = 0;
    #30;
    ce = 1;
  end
  
  initial begin
    #30;
    wr = 1;
    #10;
    rd = 1;
    #20;
    wr = 0;
    rd = 0;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #50;
    $finish;
  end
  
  sequence cewr(logic a, logic b);
    a && b;
  endsequence
  
  property p1;
    (@(posedge clk) $fell(rst) |-> cewr(ce, wr));
  endproperty
  
  property p2(logic a, logic b);
    (@(posedge clk) $fell(rst) |=> (a && b));
  endproperty
  
  CHECK_CE_WR: assert property (p1) $info("p1 CHECK_WR @ %0t", $time);
  CHECK_CE_RD: assert property (p2(ce,rd)) $info("p2 CHECK_RD @ %0t", $time);
endmodule

# KERNEL: Info: testbench.sv (52): p1 CHECK_WR @ 35
# KERNEL: Info: testbench.sv (53): p2 CHECK_RD @ 45
```
