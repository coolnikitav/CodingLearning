# Designing Sequential Logic

## Clock, D-Latch, and D Flip-Flop

D flip-flops are used for:
- Pipelining (dividing bigger blocks into smaller sections to increase throughput)
- Synchronization
- Avoid glitches/hazards
- Clock frequency
- Isolate
- Sleep mode

## D FFs vs D-latch

D-latch
- Level sensitive device

DFF
- Edge triggered

## D-Latch (Dataflow)
```
module dlatch_df(q,d,en);
  input en,d;
  output q;

  assign q = en?d:q;
endmodule
```

## D-Latch (Behavioral)
```
module dlatch_bh(q,d,en);
  input en,d;
  output reg q;

  always @(en,q)
    if (en) q = d;
endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0c37c1a9-d7ed-4e10-84f9-b79f1b4a237a)

## D Latch with Asynch Reset (Behavioral)
```
module dlatch_bh(q,d,en,rst);
  input en,d,rst;
  output reg q;

  always @(en,q,rst)
    if(rst)
      q = 1'b0;
    else if(en)
      q = d;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/195b9e6a-b879-4746-b95a-1acb42aa9acc)

## DFF (Basic)
```
module dffb(q,d,clk);
  input d,clk;
  output reg q;

  always @(posedge clk)
    if(clk)
      q <= d; // non-blocking assignment operator. = is blocking
endmodule
```

Blocking statements:
```
// These statements execute in order
a = b;
c = a;
d = c;

// They are equal to this statement:
d = b;
```

Non-blocking statements:
```
// These are concurrent statements
a <= b;
c <= a;
d <= c;
```

We will never use blocking statements to implement a DFF.

## Positive edge triggered D flip-flop with asynch active high reset
```
module dff_Pe_Ar(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always @(posedge clk or posedge rst)
    if (rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

## Negative edge triggered D flip-flop with asynch active high reset
```
module dff_Ne_Ar(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always @(negedge clk or posedge rst)
    if (rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

Negative edge triggering is used a little bit more frequently for flip flops is because even a small spike would cause the FF to get triggered:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/52d8e5ff-b91e-4b13-abe8-098f42c58814)

This scenario is a lot more rare with a line thats at one.

## Positive edge triggered DFF with asynch active low reset
```
module dff_Pe_ALr(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always @(posedge clk, negedge rst)
    if (!rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

## Positive edge triggered DFF with asynch active high set
```
module dff_Pe_Alr_Ahs(q,d,clk,rst,set);
  input d,clk,rst,set;
  output reg q;

  always@(posedge clk, negedge rst, posedge set)
    if(!rst)
      q <= 1'b0;
    else if(set)
      q <= 1'b1;
    else
      q <= d;

endmodule
```

## Synch DFF with active high reset
```
module dff_Sr(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always@(posedge clk)
    if(rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

Synch reset is the recommended way of coding.

## Synch DFF with active low reset
```
module dff_Slr(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always@(posedge clk)
    if(!rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

Reset is usually active low in real life.

## Synch DFF with reset and set
```
module dff_Slr_Shs(q,d,clk,rst,set);
  input d,clk,rst,set;
  output reg q;

  always@(posedge clk)
    if(!rst)
      q <= 1'b0;
    else if(set)
      q <= 1'b1;
    else
      q <= d;

endmodule
```

## Synch and asynch reset design
Synch reset:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/613dc9b6-5024-41b1-b2d0-cc186f216e0c)

Asynch reset:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/132697f2-1fe1-459a-9095-ffeef7386b0b)
