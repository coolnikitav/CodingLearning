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
