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
      q <= d;
endmodule
```
