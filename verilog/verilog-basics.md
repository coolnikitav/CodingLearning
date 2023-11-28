# Verilog Basics

### 3 design styles:
Dataflow
- Boolean equations
- Comb logic
- We know the circuit
- Want to infer muxes

Behavioral:
- Comb logic when we do not know the circuit or boolean expression
- All sequential elements (Latches, FFs)

Structural:
- You want to put things together (Module 1, module 2, module 3)
- Used to integrate blocks.

## My first dataflow style design
Half adder:
S = A xor B
C = A and B

A and B are inputs, S and C are outputs.

```
module HA_df(s, c, a, b);
  input a, b;
  output s, c;

  assign s = a ^ b;
  assign c = a & b;
endmodule
```

## My first behavioral style design
Half adder:
```
module HA_bh(s,c,a,b);
  input a,b;
  output reg s,c;

  always @(a,b)
    begin
      s = a ^ b;
      c = a & b;
    end
endmodule
```

reg is a datatype that helps us hold a value

By default everything is a wire

@(a,b) is the sensitivity list

## My first structural style design
Half adder (in real life we will never use structural to design a half adder):
```
module HA_st(s,c,a,b);
  input a,b;
  output s,c;

  xor xor1(s,a,b);
  and and1(c,a,b);

endmodule
```
