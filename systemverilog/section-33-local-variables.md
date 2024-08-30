# Local Variables

## Fundamentals of Local Variables
- Q: Where can we put local variables in SystemVerilog?

Used to do:
```
property p1;
  start |-> done;
endproperty
```

To use local variables:
```
property p1;
  logic i;
  (start, i++) |-> (done, i++);
endproperty
```
In the above example, i will be incremented when start is triggered and when done is triggered.

Local variables need to be either in property or sequence blocks.

## Behavior of Local Variable with Threads
- Q: Why does the count stay at 1?
  
```
module tb;
 reg clk = 0;
 reg start = 0;
 
 always #5 clk =~clk;
 
 default clocking 
 	@(posedge clk);
 endclocking
 
 always #20 start = ~start;
 
 property p1;
   logic [1:0] count = 0;
   
   ($rose(start), count++, $display("Count: %0d", count));
 endproperty
  
 assert property (@(posedge clk) p1) $info("Suc @ %0t", $time); 
 
 initial begin
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0); 
   #120;
   $finish;
 end
 
 
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 5ns, scope: tb, start-time: 5ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 15ns, scope: tb, start-time: 15ns
# KERNEL: Count: 1
# KERNEL: Info: testbench.sv (19): Suc @ 25
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 35ns, scope: tb, start-time: 35ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 45ns, scope: tb, start-time: 45ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 55ns, scope: tb, start-time: 55ns
# KERNEL: Count: 1
# KERNEL: Info: testbench.sv (19): Suc @ 65
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 75ns, scope: tb, start-time: 75ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 85ns, scope: tb, start-time: 85ns
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 95ns, scope: tb, start-time: 95ns
# KERNEL: Count: 1
# KERNEL: Info: testbench.sv (19): Suc @ 105
# ASSERT: Error: ASRT_0005 testbench.sv(19): Assertion FAILED at time: 115ns, scope: tb, start-time: 115ns
```

- A: Each separate thread has its own value.

```
module tb;
 reg clk = 0;
 reg start = 0;
 
 always #5 clk =~clk;
 
 default clocking 
 	@(posedge clk);
 endclocking
 
 always #20 start = ~start;
 
 property p1;
   logic [1:0] count = 0;
   
   // $rose(start) |-> ##[1:$] $rose(start) ##[1:$] $rose(start);
   
   ($rose(start), count = 1, $display("Count: %0d", count)) |-> ##[1:$] ($rose(start), count++, $display("Count: %0d", count)) ##[1:$] ($rose(start), count++, $display("Count: %0d", count));
 endproperty
  
 assert property (@(posedge clk) p1) $info("Suc @ %0t", $time); 
 
 initial begin
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0); 
   #130;
   $finish;
 end
 
 
endmodule

# KERNEL: Count: 1
# KERNEL: Count: 1
# KERNEL: Count: 2
# KERNEL: Count: 1
# KERNEL: Count: 2
# KERNEL: Count: 2
# KERNEL: Count: 3
# KERNEL: Info: testbench.sv (21): Suc @ 105
```

## Use Case 
Goal is to see how many clock cycles start stays on for:

```
module tb;
 reg clk = 0;
 reg start = 0;
 
 always #5 clk =~clk;
 
 default clocking 
 	@(posedge clk);
 endclocking
 
 //always #20 start = ~start;
  
 initial begin
   #20;
   start = 1;
   #60;
   start = 0;
 end
 
 property p1;
   integer count = 0;
   
   //$rose(start) |-> start[*1:$] ##1 !start;
   
   $rose(start) |-> (start, count++)[*1:$] ##1 (!start, $display("count: %0d", count));
 endproperty
  
  assert property (p1) $info("Suc @ %0t", $time); 
 
 initial begin
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0); 
   #130;
   $finish;
 end
 
 
endmodule

# KERNEL: count: 6
# KERNEL: Info: testbench.sv (28): Suc @ 85
```

```
module top(
  input [3:0] a,b,
  input clk,sample,
  output reg [4:0] s,
  output reg done
);
  reg [3:0] ta,tb;
  
  reg state = 0;
  
  always@(posedge clk)
    begin
      case(state)
       0: begin 
              if(sample == 1'b1) 
              begin
              ta <= a;
              tb <= b;
              done <= 1'b0;
              state <= 1'b1;
              end
              else
              state <= 1'b0;
         end
      1:
        begin  
          s <= ta + tb;
          done <= 1'b1;
          state <= 0;
        end
        
      default : state <= 0;  
        
      endcase
    end
  
endmodule

module tb;
  
  reg [3:0] a = 0, b = 0;
  reg clk = 0, sample = 0;
  wire [4:0] s;
  wire done;
  
  
  top dut (a,b,clk,sample,s,done);
  
  always #5 clk = ~clk;
  
 
  
  integer i = 0;
  
  initial begin
  for( i = 0; i <10; i++) begin
     @(posedge clk);
    a = $urandom();
    b = $urandom();
    sample  = 1'b1;
    @(posedge clk);
    sample  = 1'b0;
    @(posedge done);
    @(posedge clk);
  end
  end
  
  /*
  initial begin
    #8;
    sample = 1'b1;
    #10;
    sample = 1'b0;
    #15;
    sample = 1'b0;
    #10;
    sample = 1'b0;
    #15;
    sample = 1'b1;
    #10;
    sample = 1'b0;
    #15;
    
  end
  */
  property p1;
    logic [3:0] lva = 0;
    logic [3:0] lvb = 0;
    logic [4:0] lvs = 0;
    
    ($rose(sample), lva = a, lvb = b, $display("value of a: %0d and b: %0d", lva, lvb)) |-> ($rose(done)[->1], lvs = s, $display("value of output bus: %0d", lvs)) ##0 (lvs == lva + lvb);
  endproperty
    
  A1: assert property (@(posedge clk) p1) $info("suc at %0t", $time);

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0); 
    #120;
    $finish;
  end
endmodule

# KERNEL: value of a: 3 and b: 15
# KERNEL: value of output bus: 18
# KERNEL: Info: testbench.sv (56): suc at 35
# KERNEL: value of a: 0 and b: 10
# KERNEL: value of output bus: 10
# KERNEL: Info: testbench.sv (56): suc at 75
# KERNEL: value of a: 0 and b: 5
# KERNEL: value of output bus: 5
# KERNEL: Info: testbench.sv (56): suc at 115
```
