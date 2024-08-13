# Introduction to the SVA Power and IDE Usage, Course

## Power of SVA
```
module tb;
  
  reg clk = 0;
  reg a = 0;
  reg b = 0;
  
  task a_b();
    #10;
  a = 1;
    #10;
  a = 0;
    #30;
  b = 1;
    #10;
  b = 0;
    #50;
  a = 1;
    #10;
  a = 0;
    #30;
  b = 1;
    #10;
  b = 0;
    
  endtask
  
  always #5 clk =~clk;

  initial begin
    a_b();
  end

  /////////////////implementation with verilog
  
  always@(posedge clk)
    begin
      if(a == 1'b1)
         begin
           repeat(4) @(posedge clk);
           if( b == 1'b1)
             $display("Verilog Suc at %0t",$time);
           else
             $error("Verilog Failure at %0t",$time); 
         end
    end

  ////////implementation with SVA
  
  A1: assert property ( @(posedge clk)  a |-> ##4 b) $info("SVA Suc at %0t",$time);
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0); 
    #200;
    $finish;
  end

endmodule

# KERNEL: Verilog Suc at 55
# KERNEL: Info: testbench.sv (49): SVA Suc at 55
# KERNEL: Verilog Suc at 155
# KERNEL: Info: testbench.sv (49): SVA Suc at 155
```

```
module tb;
 
  
  reg clk = 0;
  reg start = 0;
  integer i = 0;
  integer count = 0;
  
  initial begin
    #80;
    start = 0;
    #10;
    start = 0;
  end

  always #5 clk =~clk; ///period 10ns  

  task check();
    for(i = 0; i < 20; i++) begin
      @(posedge clk);
      if(start == 1'b1)
         count++;
    end
  endtask  
   
 initial begin
   check();
   if(count > 0)
     $display("Verilog Suc at %0t",$time);
   else
     $error("Verilog Failure at %0t",$time);
 end
    
  /////SVA
  
  initial assert property (@(posedge clk) s_eventually start) $display("SVA Suc at %0t",$time);

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0); 
    #200;
    $finish;
  end
  
  
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(36): Assertion FAILED at time: 200ns, scope: tb, start-time: 5ns
```

```
module tb;
 
  
  reg clk = 0;
  reg rst = 0;
  
  integer i = 0;
  
  
  integer count = 0;
  int rst_count = 0;
   
  
  initial begin
    rst = 1;
    #30;
    rst = 0;
  end
  
  always #5 clk =~clk;
  
 
////////////////Verilog
 
 
 
  task countrst();
    
          @(posedge clk);
          
          for(int j = 0; j < 3 ; j++)
             begin
               if(rst)
                 rst_count++;
                 @(posedge clk);
             end
          
           for(int i = 0; i< 16; i++)
              begin
               if(rst)
                count++;
                @(posedge clk);
              end
 
  endtask
  
  
  
  task check();
    if(count == 0 && rst_count == 3)
       $display("Suc at %0t",$time);
    else
        $error("Failure at %0t",$time);  
  endtask
  
    initial begin
    countrst();
    check();
  end
  
  
  initial assert property (@ (posedge clk) rst[*3] ##1 !rst[*17]) $info("Suc at %0t",$time);
  
initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0); 
    #200;
    $finish;
  end
  
endmodule

# KERNEL: Info: testbench.sv (62): Suc at 195
```

```
module tb;
 
  
  reg clk = 0;
  reg rst = 0;
  reg wr = 0;
  reg rd = 0;
  
  integer i = 0, j = 0;
  integer hitwr = 0, hitrd = 0,err = 0;
   
  
  initial begin
    rst = 1;
    #20;
    rst = 0;
  end
  
  initial begin
    #40;
    wr = 0;
    #10;
    wr = 0;
  end
  
  initial begin
    #60;
    rd = 1;
    #10;
    rd = 0;
  end
  
  always #5 clk =~clk;
  
  default clocking 
    @(posedge clk);
  endclocking
 
////////////////Verilog
  
  task checkreset();
    repeat(2) @(posedge clk);
    for(i = 0; i< 10; i++) begin
      @(posedge clk);
      if(rst == 1'b1)
        err++;
    end
   endtask
    
    task hit();
      repeat(2) @(posedge clk);
      for(j = 0; j< 10; j++) begin
           @(posedge clk);
            if(!rst && wr)
               hitwr++;
            if(!rst && rd)
               hitrd++;
         end   
    endtask
    
  initial begin
    fork
      checkreset();
      hit();
    join  
    
    if(err == 0 && hitwr > 0 && hitrd > 0)
      $display("Verilog Suc at %0t",$time);
    else
      $error("Verilog Failure at %0t",$time);    
  end
    
 
 ///////////////////SVA
  
  initial assert property (##2 !rst |-> !rst throughout ##[0:9] wr ) $info("WR Suc at %0t",$time);
    
  initial assert property (##2 !rst |-> !rst throughout ##[0:9] rd ) $info("RD Suc at %0t",$time);
 
  
initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0); 
    #120;
    $finish;
  end
  
  
endmodule

# ASSERT: Error: ASRT_0005 testbench.sv(76): Assertion FAILED at time: 115ns, scope: tb, start-time: 5ns
```

## Behavior of the Assertion Statements in Synthesizer
![image](https://github.com/user-attachments/assets/936245c4-3df7-4f70-87cb-3dd149850be2)

Thus, we will not add assertion check to the actual logic. We will add it into a separate block:

![image](https://github.com/user-attachments/assets/c7a01b0e-2649-420c-ba8c-e9f941b6f181)

```
module synth(
input a,b,sel,
output reg y
);
 
///////Behavior check
always_comb
begin
if(sel == 1'b1)
assert (y == a) else $error("y is not equal to a");
else
assert (y == b) else $error("y is not equal to b");
end
 
/////actual RTL
always_comb
begin
if(sel == 1'b1)
y = a;
else
y = b;
end
 
endmodule
```
