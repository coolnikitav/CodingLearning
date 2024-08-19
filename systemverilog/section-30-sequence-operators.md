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
