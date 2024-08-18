# System Task
![image](https://github.com/user-attachments/assets/5c0217d5-7ef7-4450-8bfa-76d8b3add7c6)

## Use of $sampled
```
module tb;
  reg a = 1;
  reg clk = 0;
  
  always #5 clk = ~clk;
  always #5 a = ~a;
  
  // $sampled executes in prepone region, while the regular value is taken at the reactive region
  always @(posedge clk) begin
    $info("[%0t]: Value of a: %b and $sampled(a): %b", $time, a, $sampled(a));
  end
  
  // but during assertion, both of them execute in the prepone region, so they are equal
  assert property (@(posedge clk) (a == $sampled(a))) $info("Suc at %0t with a: %0b", $time, $sampled(a));
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #50;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (9): [5]: Value of a: 0 and $sampled(a): 1
# KERNEL: Info: testbench.sv (12): Suc at 5 with a: 1
# KERNEL: Info: testbench.sv (9): [15]: Value of a: 0 and $sampled(a): 1
# KERNEL: Info: testbench.sv (9): [25]: Value of a: 0 and $sampled(a): 1
# KERNEL: Info: testbench.sv (9): [35]: Value of a: 0 and $sampled(a): 1
# KERNEL: Info: testbench.sv (9): [45]: Value of a: 0 and $sampled(a): 1
# RUNTIME: Info: RUNTIME_0068 testbench.sv (19): $finish called.
```

## Understanding $rose
![image](https://github.com/user-attachments/assets/aaba646f-adbb-4629-96bb-de5aa35880d3)

```
module tb;
  reg a;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    a = 1;
    #5;
    a = 0;
    #20;
    a = 1;   
    #20;
    a = 0;
  end 
  
  always @(posedge clk) begin
    $info("[%0t]: Value of a : %0b, $sampled(a): %0b, and $rose(a): %0b", $time, a, $sampled(a), $rose(a));
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #120;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (18): [5]: Value of a : 0, $sampled(a): 1, and $rose(a): 1
# KERNEL: Info: testbench.sv (18): [15]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [25]: Value of a : 1, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [35]: Value of a : 1, $sampled(a): 1, and $rose(a): 1
# KERNEL: Info: testbench.sv (18): [45]: Value of a : 0, $sampled(a): 1, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [55]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [65]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [75]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [85]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [95]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [105]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
# KERNEL: Info: testbench.sv (18): [115]: Value of a : 0, $sampled(a): 0, and $rose(a): 0
```

## $rose with multi-bit signal
```
module tb;
  reg [3:0] b;
  reg clk = 0; 
  
  always #5 clk = ~clk;
  
  initial begin
    b = 4'b0100;
    #10;
    b = 4'b0101;
    #10;
    b = 4'b0100;
    #10;
    b = 4'b0110;
    #10;
    b = 4'b0100;
    #10;
    b = 4'b0101;
    #10;
    b = 4'b0000;
  end
  
  // $rose looks at LSB
  always @(posedge clk) begin
    $info("[%0t]: Value of b: %04b and $rose(b): %0b", $time, $sampled(b), $rose(b));
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #80;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (25): [5]: Value of b: 0100 and $rose(b): 0
# KERNEL: Info: testbench.sv (25): [15]: Value of b: 0101 and $rose(b): 1
# KERNEL: Info: testbench.sv (25): [25]: Value of b: 0100 and $rose(b): 0
# KERNEL: Info: testbench.sv (25): [35]: Value of b: 0110 and $rose(b): 0
# KERNEL: Info: testbench.sv (25): [45]: Value of b: 0100 and $rose(b): 0
# KERNEL: Info: testbench.sv (25): [55]: Value of b: 0101 and $rose(b): 1
# KERNEL: Info: testbench.sv (25): [65]: Value of b: 0000 and $rose(b): 0
# KERNEL: Info: testbench.sv (25): [75]: Value of b: 0000 and $rose(b): 0
```

## Specifying Clock for the Sample Function
