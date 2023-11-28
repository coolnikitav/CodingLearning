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

## 1-bit full adder (structural 1)
S = A xor B xor Cin

C = (A and B) or (B and Cin) or (Cin and A)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b313b48b-2daa-4870-868c-251fbd5fa664)


```
module FA_st(s,c,a,b,cin);
  input a,b,cin;
  output s,c;

  wire n1,n2,n3,n4;

  xor xor1(n1,a,b);
  xor xor2(s,n1,cin);

  and and1(n2,a,b);
  and and2(n3,b,cin);
  and and3(n4,cin,a);

  or or1(c,n2,n3,n4);
endmodule
```

## 1-bit full adder (structural 2)
Using 2 half adders:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f97ea989-fc54-400c-929b-35212998cbd8)

```
module FA_st2(s,c,a,b,cin);
  input a,b,cin;
  output s,c,;

  wire n1,n2,n3;

  HA_df HA_df_1(n1,n2,a,b);
  HA_df HA_df_2(s,n3,n1,cin);
  or or1(c,n3,n2);
endmodule
```

## 1-bit full adder (structural 3)

```
module fa_st(ss,cc,aa,bb,cin);
  input aa,bb,cin;
  output ss,cc;

  wire n1,n2,n3;

  HA_df HA_df_1(.s(n1), .c(n2), .a(aa), .b(bb));
  HA_df HA_df_2(.c(n3), .s(ss), .b(cin), .a(n1));
  or or1(cc, n2, n3);
endmodule
```

## 1-bit full adder (dataflow)

S = A xor B xor Cin

C = (A and B) or (B and Cin) or (Cin and A)

```
module FA_df(s,c,a,b,cin);
  input a,b,cin;
  output s,c;

  assign s = a ^ b ^ cin;
  assign c = a & b | b & cin | cin & a;
endmodule
```

## 1-bit full adder (behavioral)
```
module FA_bh(s,c,a,b,cin);
  input a,b,cin;
  output reg s,c;

  always @(*)
    begin
      s = a ^ b ^ cin;
      c = a & b | b & cin | cin & a;
    end
endmodule
```

You can use a * if all of the inputs are going into the sensitivity list
