# Working With Multiple Sequences

## Fundamentals of Boolean Operators
boolean operators
- and
- or
- not

```
sequence s1;
  a[*1];
endsequence

sequence s2;
  b[*2];
endsequence

assert (@(posedg clk) $rose(start) |-> s1 and s2);
```

## Usage of AND Operator
If start is asserted, both a and b should remain high for 2 consecutive clock ticks. b will become high in the next clock tickk after a becomes high
```
module tb;
  reg start = 0;
  reg a = 0, b = 0;
  reg done = 0;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    #30;
    start = 1;
    #10;
    start = 0;
  end
  
  initial begin
    #60;
    done = 1;
    #10;
    done = 0;
  end
  
  initial begin
    #30;
    a = 1;
    #20;
    a = 0;
  end
  
  initial begin
    #40;
    b = 1;
    #20;
    b = 0;
  end
  
  sequence sa;
    a[*2];
  endsequence
  
  sequence sb;
    ##1 b[*2];
  endsequence
  
  assert property (@(posedge clk) $rose(start) |-> sa and sb) $info("Suc at %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #100;
    $finish;
  end
endmodule

# KERNEL: Info: testbench.sv (45): Suc at 55
```

## Usage of OR operator
```
sequence sa;
  a[*2];
endsequence

sequence sb;
  b[*2];
endsequence

assert property (@(posedge clk) $rose(start) |-> sa or sb) $info("Suc at %0t", $time);

# KERNEL: Info: testbench.sv (45): Suc at 45
```

## Use Case
```
module tb;
  reg clk = 0, rd, wr, start;
  
  always #5 clk = ~clk;
  
  initial begin
    start = 0;
    #20;
    start = 1;
    #10;
    start = 0;
  end
  
  initial begin
    wr = 0;
    #30;
    wr = 1;
    #10;
    wr = 0;
  end
  
  initial begin
    rd = 0;
    #40;
    rd = 1;
    #20;
    rd = 0;
  end
  
  sequence swr;
    wr[*1];
  endsequence
  
  sequence srd;
    ##1 rd[*2];
  endsequence
  
  sequence wrrd;
    strong(##[0:$] wr && rd);
  endsequence
  
  // at least single read and write cycle during simulation
  A1: assert property (@(posedge clk) $rose(start) |=> swr and srd) $info("suc at %0t", $time);
    
  // read and write should not occur at same time
    A2: assert property (@(posedge clk) $rose(start) |=> not(wrrd)) $info("A2 suc at %0t", $time);
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #110;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (43): suc at 55
# RUNTIME: Info: RUNTIME_0068 testbench.sv (53): $finish called.
# KERNEL: Time: 110 ns,  Iteration: 0,  Instance: /tb,  Process: @INITIAL#48_4@.
# KERNEL: stopped at time: 110 ns
# VSIM: Simulation has finished. There are no more test vectors to simulate.
# KERNEL: Info: testbench.sv (46): A2 suc at 110
```

## Matching Operators
- throughout - signal must be true for the entire duration of the sequence
- within - test sequence must lie inside of the reference sequence
- intersect - both test and reference sequences have the same start and end endpoints

## Usage of Throughout
```
module tb;
 reg a = 0, b = 0, c = 0; //Data Signal
 reg clk = 0; // Clock 
 
 always #5 clk = ~clk; ///Generation of 10 ns Clock
 
 initial begin
   #28;
   b = 1;
   #30;
   b= 0; 
 end
 
 initial begin
   #63;
   c = 1;
   #10;
   c= 0; 
 end

 initial begin
   #28;
   a = 1;
   #40;
   a = 0; 
 end

 sequence seq_bc;
   b[*3] ##1 c; 
 endsequence
  
  A1: assert property (@(posedge clk) $rose(b) |-> a throughout seq_bc) $info("suc @ %0t", $time);
  
 initial begin
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0);
   #150;
   $finish;
 end
endmodule

# KERNEL: Info: testbench.sv (32): suc @ 65
```

## Within Operator 
```
module tb;
 reg a = 0, b = 0, c = 0; //Data Signal
 reg clk = 0; // Clock 
 
 always #5 clk = ~clk; ///Generation of 10 ns Clock 
 
 initial begin
   #28;
   b = 1;
   #30;
   b= 0; 
 end 
 
 initial begin
   #63;
   c = 1;
   #10;
   c= 0; 
 end
 
 initial begin
   #28;
   a = 1;
   #40;
   a = 0; 
 end
 
 /////////reference sequence
 
 sequence seq_bc;
   b[*3] ##1 c;
 endsequence
 
 sequence seq_a;
   a[*4];
 endsequence
  
 A1: assert property (@(posedge clk) $rose(b) |-> seq_a within seq_bc) $info("Suc @ %0t", $time);
 
 initial begin
   $assertvacuousoff(0);
   $dumpfile("dump.vcd");
   $dumpvars;
   #150;
   $finish;
 end 
endmodule

# KERNEL: Info: testbench.sv (38): Suc @ 65
```

## Intersect Operator
```
module tb;
 reg a = 0, b = 0, c = 0; //Data Signal
 reg clk = 0; // Clock 
 
 always #5 clk = ~clk; ///Generation of 10 ns Clock 
 
 initial begin
   #28;
   b = 1;
   #30;
   b= 0; 
 end 
 
 initial begin
   #63;
   c = 1;
   #10;
   c= 0; 
 end
 
 initial begin
   #28;
   a = 1;
   #40;
   a = 0; 
 end
 
 /////////reference sequence
 
 sequence seq_bc;
   b[*3] ##1 c;
 endsequence
 
 sequence seq_a;
   a[*4];
 endsequence
  
 A1: assert property (@(posedge clk) $rose(b) |-> seq_a intersect seq_bc) $info("Suc @ %0t", $time);
 
 initial begin
   $assertvacuousoff(0);
   $dumpfile("dump.vcd");
   $dumpvars;
   #150;
   $finish;
 end 
endmodule

# KERNEL: Info: testbench.sv (38): Suc @ 65
```

## Use Cases
![image](https://github.com/user-attachments/assets/27d72d3b-0e8c-4b45-9345-8a61d1ec0fd9)
```
assert property (@(posedge clk) CE |=> (dout == $past(dout+1)));
```

![image](https://github.com/user-attachments/assets/1c4dfc10-c98c-4750-b06f-f90b1318988d)
```
sequence seq_a;
  a[->2];
endsequence

sequence seq_b;
  b[->3];
endsequence

assert property(@(posedge clk) $rose(start) |-> seq_a intersect seq_b);
```

![image](https://github.com/user-attachments/assets/e9cf9f88-67d7-4c27-88ed-d340013cce64)
```
assert property(@(posedge clk) $rose(start) |-> a throughout b[->3]);
```

![image](https://github.com/user-attachments/assets/89327c70-93a8-4b1b-b71d-50ef001a306e)

![image](https://github.com/user-attachments/assets/d2bcce9d-8e93-4b1b-a30c-210e1014d47a)

![image](https://github.com/user-attachments/assets/d6ec4f08-647c-4ca7-8fbc-d28990fbf0aa)

![image](https://github.com/user-attachments/assets/e6378769-394b-4634-95ae-e4d129a4fcac)
