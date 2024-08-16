# Getting Started With Concurrent Assertion

## Layers in Concurrent Assertions
![image](https://github.com/user-attachments/assets/b9df12c8-342b-4d1b-ac97-fa7f0f3b735d)

![image](https://github.com/user-attachments/assets/c3a2a22d-b7dd-44d6-80cb-1e3ce0f65ba2)

## Allowed Operators in Each Layer
![image](https://github.com/user-attachments/assets/c2230055-d5fa-4ab3-9978-ef4b53b0c420)

## Format of Concurrent Assertion
![image](https://github.com/user-attachments/assets/5bc87d03-6fcf-4b61-a062-b8ad78eb8693)

![image](https://github.com/user-attachments/assets/c686aae3-0e8f-42b5-bc31-bfd7e704f298)

## Single or Multiple Evaluation of Property
![image](https://github.com/user-attachments/assets/82342380-4cd8-41f2-ab8a-0edaa9474561)

![image](https://github.com/user-attachments/assets/ad9d25c4-d2de-4a75-bbc4-8e6cba0c24be)

## Demonstration
```
module tb;
  reg clk = 0;
  reg temp = 0;
  reg a = 0;
  
  initial begin
    temp = 1;
    @(posedge clk);
    temp = 0;
  end
  
  always #10 clk = ~clk;
  always #40 a = ~a;
  
  A1: assert property (@(posedge clk) (a == 1'b1)) $info("A1 Suc @ %0t", $time); else $error("A1 fail @ %0t", $time);
    
  initial A2: assert property (@(posedge clk) (a == 1'b1)) $info("A2 Suc @ $0t", $time); else $error("A2 Fail @ %0t", $time);
      
  A3: assert property (@(posedge clk) $rose(temp) |-> (a == 1'b1)) $info("A3 Suc @ %0t", $time); else $error("A3 Fail @ %0t", $time);
    
  initial begin
    repeat(10) @(posedge clk);
    $finish;
  end
    
  initial begin
    $assertvacuousoff(0);
    #100;
    $finish();
  end
endmodule

# KERNEL: Error: testbench.sv (15): A1 fail @ 10
# KERNEL: Error: testbench.sv (17): A2 Fail @ 10
# KERNEL: Error: testbench.sv (19): A3 Fail @ 10
# KERNEL: Info: testbench.sv (15): A1 Suc @ 50
# KERNEL: Error: testbench.sv (15): A1 fail @ 90
```

## Understanding Clock Edges
```
module tb;
  reg rst = 0;
  reg en = 1;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #7;
    rst = 0;
    #5;
    rst = 1;
  end
  
  CHECL_POSEDGE: assert property (@(posedge clk) en |-> rst) $info("POSEDGE SUC @ %0t", $time); else $error("POSEDGE Fail @ %0t", $time);
  CHECL_NEGEDGE: assert property (@(negedge clk) en |-> rst) $info("NEGEDGE SUC @ %0t", $time); else $error("NEGEDGE Fail @ %0t", $time);
  CHECL_BOTHEDGE: assert property (@(edge clk) en |-> rst) $info("EDGE SUC @ %0t", $time); else $error("EDGE Fail @ %0t", $time);
    
  initial begin
    #20;
    $finish;
  end
endmodule

# KERNEL: Info: testbench.sv (16): POSEDGE SUC @ 5
# KERNEL: Info: testbench.sv (18): EDGE SUC @ 5
# KERNEL: Error: testbench.sv (17): NEGEDGE Fail @ 10
# KERNEL: Error: testbench.sv (18): EDGE Fail @ 10
# KERNEL: Info: testbench.sv (18): EDGE SUC @ 15
```

## Default Clocking
```
module tb;
  reg clk = 0;
  reg req = 1;
  reg ack = 0;

  initial begin
    #5;
    ack = 1;
    #5;
    ack = 0;
  end

  always #2 clk = ~clk;

  clocking c1
  	@(posedge clk);
  endclocking


  clocking c2
  	@(negedge clk);
  endclocking


  /*
  default clocking c1
  @(posedge clk);
  endclocking
  */

  default clocking c1;
 
  A1 : assert property ( req |-> ack) $info("A1 Suc at %0t", $time);
  A2 : assert property ( req |-> ack) $info("A2 Suc at %0t", $time);
  A3 : assert property ( req |-> ack) $info("A3 Suc at %0t", $time);

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #20;
    $finish();
  end
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(33): Assertion "A1" FAILED at time: 2ns, scope: tb, start-time: 2ns
# ASSERT: Error: ASRT_0005 testbench.sv(34): Assertion "A2" FAILED at time: 2ns, scope: tb, start-time: 2ns
# ASSERT: Error: ASRT_0005 testbench.sv(35): Assertion "A3" FAILED at time: 2ns, scope: tb, start-time: 2ns
# KERNEL: Info: testbench.sv (33): A1 Suc at 6
# KERNEL: Info: testbench.sv (34): A2 Suc at 6
# KERNEL: Info: testbench.sv (35): A3 Suc at 6
# ASSERT: Error: ASRT_0005 testbench.sv(33): Assertion "A1" FAILED at time: 14ns, scope: tb, start-time: 14ns
# ASSERT: Error: ASRT_0005 testbench.sv(34): Assertion "A2" FAILED at time: 14ns, scope: tb, start-time: 14ns
# ASSERT: Error: ASRT_0005 testbench.sv(35): Assertion "A3" FAILED at time: 14ns, scope: tb, start-time: 14ns
```

## Disabling Concurrent Assertion
```
module tb;
  reg clk = 0;
  reg req = 0;
  reg ack = 0;
  reg rst = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #50;
    rst = 0;
  end
  
  initial begin
    #30;
    req = 1;
    #10;
    req = 0;
    #30;
    req = 1;
    #10;
    req = 0;
    ack = 1;
    #10;
    ack = 0;
  end
  
  // Ways to disable check for concurrent assertions
  A2: assert property ( @(posedge clk) disable iff(rst) req |=> ack) $info("Suc at %0t", $time);
    
  initial begin
    #100;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (30): Suc at 55
# KERNEL: Info: testbench.sv (30): Suc at 65
# KERNEL: Info: testbench.sv (30): Suc at 85
# KERNEL: Info: testbench.sv (30): Suc at 85
# KERNEL: Info: testbench.sv (30): Suc at 95
```
