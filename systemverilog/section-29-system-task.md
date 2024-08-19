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
```
assert property (@(posedge clk) $rose(a));
assign c = $rose(a, @(posedge clk));
```

## Understanding $fell
![image](https://github.com/user-attachments/assets/1ca19b2b-6079-46f3-877a-6efc9d3a7645)

## $fell with Single bit signal
```
module tb;
  reg a = 1;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 20; i++) begin
      a = $urandom_range(0,1);
      #5;
    end
  end
  
  always @(posedge clk) begin
    $info("[%0t]: Value of a: %0b and $fell(a): %0b", $time, $sampled(a), $fell(a));
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #120;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (15): [5]: Value of a: 1 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [15]: Value of a: 0 and $fell(a): 1
# KERNEL: Info: testbench.sv (15): [25]: Value of a: 0 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [35]: Value of a: 0 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [45]: Value of a: 1 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [55]: Value of a: 0 and $fell(a): 1
# KERNEL: Info: testbench.sv (15): [65]: Value of a: 1 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [75]: Value of a: 0 and $fell(a): 1
# KERNEL: Info: testbench.sv (15): [85]: Value of a: 1 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [95]: Value of a: 1 and $fell(a): 0
# KERNEL: Info: testbench.sv (15): [105]: Value of a: 0 and $fell(a): 1
# KERNEL: Info: testbench.sv (15): [115]: Value of a: 0 and $fell(a): 0
```

## $fell with Single bit and Multibit signal
```
module tb;
 reg [3:0] b;////xxxx
 reg clk = 0;

 always #5 clk = ~clk;

 initial begin
   b = 4'b0100;
   #10;
   b = 4'b0101;
   #10;
   b = 4'b0100;
   #10;
   b = 4'b0101;
   #10;
   b = 4'b0100;
   #10;
   b = 4'b0101;
   #10;
   b = 4'b0000;
 end
 
 always@(posedge clk)
   begin
     $info("Value of b :%0b and $fell(b) : %0b", $sampled(b), $fell(b));
   end 

 initial begin
   $dumpfile("dump.vcd"); 
   $dumpvars;
   #60;
   $finish();
 end
endmodule

# KERNEL: Info: testbench.sv (30): Value of b :100 and $fell(b) : 1
# KERNEL: Info: testbench.sv (30): Value of b :101 and $fell(b) : 0
# KERNEL: Info: testbench.sv (30): Value of b :100 and $fell(b) : 1
# KERNEL: Info: testbench.sv (30): Value of b :101 and $fell(b) : 0
# KERNEL: Info: testbench.sv (30): Value of b :100 and $fell(b) : 1
# KERNEL: Info: testbench.sv (30): Value of b :101 and $fell(b) : 0
```

## Understanding $past 
![image](https://github.com/user-attachments/assets/e45e709a-0f7d-40cd-9cc9-a2c39c0e2bdf)

![image](https://github.com/user-attachments/assets/c0c59ca7-db4d-495a-87bb-e2e14012029e)

```
module tb;
  reg a = 1, clk = 0;
  
  reg en = 0;
  reg [3:0] b = 2;
  
  always #5 clk = ~clk; 
  
  initial begin
    en = 1;
    #100;
    en = 0;
  end
  
  initial begin
    for (int i = 0; i < 15; i++) begin
      b = $urandom_range(0,20);
      a = $urandom_range(0,1);
      @(posedge clk);
    end
  end
  
  always @(posedge clk) begin
    $display("[%0t]: Value of a: %0d and b: %0d", $time, $sampled(a), $sampled(b));
    $display("[%0t]: Value of $past(a): %0d, $past(b): %0d", $time, $past(a), $past(b));
    $display("---------------------------------");
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150;
    $finish();
  end
endmodule

# KERNEL: [5]: Value of a: 1 and b: 7
# KERNEL: [5]: Value of $past(a): 1, $past(b): 2
# KERNEL: ---------------------------------
# KERNEL: [15]: Value of a: 1 and b: 7
# KERNEL: [15]: Value of $past(a): 1, $past(b): 7
# KERNEL: ---------------------------------
# KERNEL: [25]: Value of a: 1 and b: 8
# KERNEL: [25]: Value of $past(a): 1, $past(b): 7
# KERNEL: ---------------------------------
# KERNEL: [35]: Value of a: 1 and b: 3
# KERNEL: [35]: Value of $past(a): 1, $past(b): 8
# KERNEL: ---------------------------------
# KERNEL: [45]: Value of a: 1 and b: 13
# KERNEL: [45]: Value of $past(a): 1, $past(b): 3
# KERNEL: ---------------------------------
# KERNEL: [55]: Value of a: 0 and b: 3
# KERNEL: [55]: Value of $past(a): 1, $past(b): 13
# KERNEL: ---------------------------------
# KERNEL: [65]: Value of a: 1 and b: 5
# KERNEL: [65]: Value of $past(a): 0, $past(b): 3
# KERNEL: ---------------------------------
# KERNEL: [75]: Value of a: 1 and b: 10
# KERNEL: [75]: Value of $past(a): 1, $past(b): 5
# KERNEL: ---------------------------------
# KERNEL: [85]: Value of a: 1 and b: 12
# KERNEL: [85]: Value of $past(a): 1, $past(b): 10
# KERNEL: ---------------------------------
# KERNEL: [95]: Value of a: 1 and b: 1
# KERNEL: [95]: Value of $past(a): 1, $past(b): 12
# KERNEL: ---------------------------------
# KERNEL: [105]: Value of a: 1 and b: 12
# KERNEL: [105]: Value of $past(a): 1, $past(b): 1
# KERNEL: ---------------------------------
# KERNEL: [115]: Value of a: 0 and b: 9
# KERNEL: [115]: Value of $past(a): 1, $past(b): 12
# KERNEL: ---------------------------------
# KERNEL: [125]: Value of a: 0 and b: 2
# KERNEL: [125]: Value of $past(a): 0, $past(b): 9
# KERNEL: ---------------------------------
# KERNEL: [135]: Value of a: 0 and b: 8
# KERNEL: [135]: Value of $past(a): 0, $past(b): 2
# KERNEL: ---------------------------------
# KERNEL: [145]: Value of a: 0 and b: 0
# KERNEL: [145]: Value of $past(a): 0, $past(b): 8
# KERNEL: ---------------------------------
```

```
always @(posedge clk) begin
  $display("[%0t]: Value of a: %0d, b: %0d, and en: %0d", $time, $sampled(a), $sampled(b), $sampled(en));
  $display("[%0t]: Value of $past(a): %0d, $past(b): %0d", $time, $past(a,1,en), $past(b,1,en));
  $display("---------------------------------");
end

# KERNEL: [5]: Value of a: 1, b: 7, and en: 1
# KERNEL: [5]: Value of $past(a): 1, $past(b): 2
# KERNEL: ---------------------------------
# KERNEL: [15]: Value of a: 1, b: 7, and en: 1
# KERNEL: [15]: Value of $past(a): 1, $past(b): 7
# KERNEL: ---------------------------------
# KERNEL: [25]: Value of a: 1, b: 8, and en: 1
# KERNEL: [25]: Value of $past(a): 1, $past(b): 7
# KERNEL: ---------------------------------
# KERNEL: [35]: Value of a: 1, b: 3, and en: 1
# KERNEL: [35]: Value of $past(a): 1, $past(b): 8
# KERNEL: ---------------------------------
# KERNEL: [45]: Value of a: 1, b: 13, and en: 1
# KERNEL: [45]: Value of $past(a): 1, $past(b): 3
# KERNEL: ---------------------------------
# KERNEL: [55]: Value of a: 0, b: 3, and en: 1
# KERNEL: [55]: Value of $past(a): 1, $past(b): 13
# KERNEL: ---------------------------------
# KERNEL: [65]: Value of a: 1, b: 5, and en: 1
# KERNEL: [65]: Value of $past(a): 0, $past(b): 3
# KERNEL: ---------------------------------
# KERNEL: [75]: Value of a: 1, b: 10, and en: 1
# KERNEL: [75]: Value of $past(a): 1, $past(b): 5
# KERNEL: ---------------------------------
# KERNEL: [85]: Value of a: 1, b: 12, and en: 1
# KERNEL: [85]: Value of $past(a): 1, $past(b): 10
# KERNEL: ---------------------------------
# KERNEL: [95]: Value of a: 1, b: 1, and en: 1
# KERNEL: [95]: Value of $past(a): 1, $past(b): 12
# KERNEL: ---------------------------------
# KERNEL: [105]: Value of a: 1, b: 12, and en: 0
# KERNEL: [105]: Value of $past(a): 1, $past(b): 1
# KERNEL: ---------------------------------
# KERNEL: [115]: Value of a: 0, b: 9, and en: 0
# KERNEL: [115]: Value of $past(a): 1, $past(b): 1
# KERNEL: ---------------------------------
# KERNEL: [125]: Value of a: 0, b: 2, and en: 0
# KERNEL: [125]: Value of $past(a): 1, $past(b): 1
# KERNEL: ---------------------------------
# KERNEL: [135]: Value of a: 0, b: 8, and en: 0
# KERNEL: [135]: Value of $past(a): 1, $past(b): 1
# KERNEL: ---------------------------------
# KERNEL: [145]: Value of a: 0, b: 0, and en: 0
# KERNEL: [145]: Value of $past(a): 1, $past(b): 1
# KERNEL: ---------------------------------
```

## Typical Use Cases
- If a assert, b must assert in next clock tick
  - assert property (@(posedge clk) $rose(a) |=> $rose(b));
- Each new request must be followed by acknowledgement
  - assert property (@(posedge clk) $rose(req) |=> $rose(ack));
- If rst dessert, CE must assert in same clock tick
  - assert property (@(posedge clk) $fell(rst) |-> $rose(CE));
- wr request must be followed by rd request
  - assert property (@(posedge clk) $rose(wr) |=> $rose(rd));
- current value of addr must be one greater than the previous value if start assert
  - $rose(start) |=> (addr == $past(addr) + 1)
- if rst dessert, dout must be zero
  - $fell(rst) |-> (dout == 0)
- if loadin dessert, dout must be equal to load value
  - $fell(loadin) |-> (dout == load)
- if rst dessert, output of the shift register must be shifted to left by one in the next clock tick
  - $fell(rst) |=> (sout == {sout[6:0],0});
- if rst dessert, current value and past value of the signal differ only in single bit
  - $fell(rst) |=> $onehot(a^$past(a));
- in DFF, output must remain constant if CE is low
  - $fell(CE) |=> (out == $past(out));
- in TFF, if CE assert output must toggle
  - $rose(CE) |=> (out != $past(out));

## $changed + $stable
```
module tb;
  reg a = 0;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 15; i++) begin
      a = $urandom_range(0,1);
      @(posedge clk);
    end
  end
  
  always @(posedge clk) begin
    $display("[%0t]: Value of a: %0b $changed(a): %0b $stable(a): %0b", $time, a, $changed(a), $stable(a));
    $display("----------------------------------------");
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish;
  end
endmodule

# KERNEL: [5]: Value of a: 1 $changed(a): 1 $stable(a): 0
# KERNEL: ----------------------------------------
# KERNEL: [15]: Value of a: 1 $changed(a): 0 $stable(a): 1
# KERNEL: ----------------------------------------
# KERNEL: [25]: Value of a: 0 $changed(a): 1 $stable(a): 0
# KERNEL: ----------------------------------------
# KERNEL: [35]: Value of a: 0 $changed(a): 0 $stable(a): 1
# KERNEL: ----------------------------------------
# KERNEL: [45]: Value of a: 0 $changed(a): 0 $stable(a): 1
# KERNEL: ----------------------------------------
# KERNEL: [55]: Value of a: 1 $changed(a): 1 $stable(a): 0
# KERNEL: ----------------------------------------
# KERNEL: [65]: Value of a: 0 $changed(a): 1 $stable(a): 0
# KERNEL: ----------------------------------------
# KERNEL: [75]: Value of a: 0 $changed(a): 0 $stable(a): 1
# KERNEL: ----------------------------------------
# KERNEL: [85]: Value of a: 1 $changed(a): 1 $stable(a): 0
# KERNEL: ----------------------------------------
# KERNEL: [95]: Value of a: 0 $changed(a): 1 $stable(a): 0
# KERNEL: ----------------------------------------
```
