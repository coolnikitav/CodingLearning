# Procedural Constructs

## Types of signals in testbenches
- Global signal (clk, rst)
- Data signal (rdata,wdata)
- Control signal (raddr,waddr,WR,OE)

## Initial block
Starts execution at time 0 (as soon as simulation starts).

```
`timescale 1ns/1ps

module tb;

  reg a = 0;

  // single statement
  initial a = 1;

  // multiple statements
  initial begin
    a = 1;
    #10;
    a = 0;
  end
  
endmodule
```

```
`timescale 1ns/1ps

module tb();

  // global signal clk,rst
  
  reg clk,rst;
  
  reg [3:0] temp;
  
  // 1.Initialize global variables
  initial begin
  	clk = 1'b0;
    rst = 1'b0;
  end
  
  // 2.Random signal for data/control
  initial begin
    rst = 1'b1;
    #30;
    rst = 1'b0;
  end
  
  initial begin
    temp = 4'b0100;
    #10;
    temp = 4'b1100;
    #10;
    temp = 4'b0011;
    #10;
  end
  
  // 3.System task at the start of simulation
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
  
  // 4.Analyzing values of variables on console
  initial begin
    $monitor("Temp : %0d at time : %0t", temp, $time);
  end
  
  // 5.Stop simulation by forecfully calling finish.
  initial begin
    #200;
    $finish();
  end
  
endmodule
```

## Always Block
- Comb: always @ (a,b)
- Seq: always @ (posedge clk)

```
`timescale 1ns / 1ps
 
module tb();
 
  
  reg clk; //initial value = X
  
  reg clk50;
  reg clk25 = 0;  ///initialize variable
  
 
  initial begin
    clk = 1'b0;
    rst = 1'b0;
    clk50 = 0;
    
  end
 
  
  always #5 clk = ~clk; //100 MHz
  
  always #10 clk50 = ~clk50;  ///50 MHz
  
  always #20 clk25 = ~clk25;  ///25 MHz
  
  
  
  
 
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
 
  initial begin
    #200;
    $finish();
  end
  
endmodule
```

```
// Synchronizing clock edges
  always #5 clk = ~clk;
  
  always begin
    #5;
    clk50 = 1;
    #10;
    clk50 = 0;
    #5;
  end
  
  always begin
    #5;
    clk25 = 1;
    #20;
    clk25 = 0;
    #15;
  end
```

If your system needs, for example 16 MHz => Period = 62.5 nsec => Half period = 31.25 nsec or 8 MHz => Period = 125 nsec => Half period = 62.5 nsec, you need to have enough precision.

In 
```
`timescale 1ns/1ps
```
1ns is the time unit and 1ps is the time precision. So you can have up to log10(1ns/1ps) = log10(1000) = 3 decimal points.

31.25 will stay 31.25, but 31.4567 will be rounded to 31.457.
```
//`timescale 1ns / 1ns // cannot have any decimal
`timescale 1ns / 1ps
 
module tb();
 
  reg clk16 = 0;
  reg clk8 = 0;
  
  always #31.25 clk16 = ~clk16;
  always #62.5 clk8 = ~clk8;
 
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
 
  initial begin
    #200;
    $finish();
  end
  
endmodule
```

## Parameters for generating clock
- Frequency: period = 1/freq
- Duty cycle
- Phase diff: how much it is shifted with relation to other clocks
```
`timescale 1ns / 1ps

module tb();

    reg clk = 0;
    reg clk50 = 0;
    
    always #5 clk = ~clk;   // 100 MHz
    
    /*
    real phase = 10;
    real t_on = 5;
    real t_off = 5;
    */
    
    task calc (input real freq_hz, input real duty_cycle, input real phase, output real pout, output real t_on, output real t_off);real
        pout = phase;
        t_on = (1.0/freq_hz) * duty_cycle * 1000_000_000;
        t_off = (1000_000_000 / freq_hz) - t_on;
    endtask
    
    task clkgen(input real phase, input real t_on, input real t_off);
        @(posedge clk);
        #phase;  // delay
        while (1) begin
            clk50 = 1;
            #t_on;
            clk50 = 0;
            #t_off;
        end
    endtask
    
    real phase;
    real t_on;
    real t_off;
    
    initial begin
        calc(100_000_000, 0.1, 2, phase, t_on, t_off);
        clkgen(phase, t_on, t_off);
    end
    
    initial begin
        #200;
        $finish();
    end
    
endmodule
```
