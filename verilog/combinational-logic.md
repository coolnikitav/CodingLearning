# Designing Combinational Logic

## Valued Logic
Verilog has 4-valued logic: 0, 1, X, Z

0: 
- Logic zero (a = 0)
- Strong zero (line that can ground everything on that line)
- False case
- Low state

1:
- Logic one (a = 1)
- Strong one (line that can pull everything on that line to Vdd)
- True case
- High state

X (does not occur in real life, we just don't know whether the value is 1 or 0. It is mainly for simulation purposes):
- Unknown (an input is unknown, and output cannot be determined)
- Conflict (two people writing different values to the same line. Happens often in simulation)
- Metastability (for example, setup or hold times are violated in a FF)
- Uninitialized (mostly for FF, clock hasnt arrived, before first clock)

Z:
- High impedance (see in tri state buffers. It has an enable, input A, and output Y. When E = 1, Y = A. When E = 0, Y = 'Z'. Means nothing is driven on this line, like a free disconnected wire, no voltage).

VHDL has 9 values.

## Data types
2 major data types:

wire
 - default input, output
 - need to explicitely declare wire is when you use structural. For example, between a module and a gate (between modules and primitives). Need to name wires n1,n2...

reg
 - Only used in behavioral blocks: always, initial

## Number Representation
When you defined a number, the default size is 32 bit binary.

<size><base><number>

- Decimal (default) -> 10'd8 (0000001000)
- Hex -> 9'hfe (011111110)
- Binary -> 8'b1100 (00001100)
- Octal -> 7'o67 (0110111)

7'hfe (1111110) - truncates bits

Can use _ for better readibility

32'habcd_efab;

Negative numbers:

6 bit x wire = -6b'1_1011 (The num is 011011. We take 2's complement, so number stored will be 100101)

4 bit x wire = -6b'1_1011 (It will truncate 100101 to 0101 and store it in x)

8 bit x wire = -6b'1_1011 (x will store 11100101. So the number is sign extended)

Valid number (only for simulation. Cannot synthesize):

y = 5'b0_1zox

6 bit wire y = 5'bz_1011; (Gets sign extended to zz1011)

8 bit wire y = 5'bx_0011; (Gets sign extended to xxxx0011)

## Bit and bus
```
input x,y; // both are single bits

wire a,b; // both are single bits

reg c,d; // both are single bits

input [3:0]x; // bus, x[3] is MSB, x[0] is LSB
a = x[0]; // LSB of x
b = x[3]; // MSB of x

wire [1:0]w;
w = x[2:1]; 

wire [0:7]w; // w[7] is LSB, w[0] is MSB
```
## Naming Conventions
If our file name is ha.v, we want our module name to be "ha"

Module name 
 - Start with a letter (lower case)
 - Can contain numbers and underscores (full_adder_4_bit)

## Operators - Bitwise
Work on each bit of the wire

```
wire a,b,c;
wire [3:0]w,x,y;

// not - used to complement
a = ~b; // b gets inverted and flows to a
x = ~y; // each bit of y gets inverted and becomes x

// and - masking bits (for example you want to extract the last 2 bits: you apply ...00011),
// force reset (pick which bits you want to reset)
a = b & c;
x = w & y; // each bit is anded together and become x

// or - mask (set bits you want to 1),
// force set values
a = b | c;
x = w | y; // 4 or gates

// xor - selectively complement certain bits 
a = b ^ c;
x = w ^ y;

// xnor - see which bits match
a = b ~^ c;
x = w ~^ y;

// nor - force 0 and flip bits (use 1 to force 0 and 0 to flip bits)
a = b ~| c;
x = w ~| y;

// nand - force 1 and flip bits (use 0 to force 1 and 1 to flip bits)
a = b ~& c;
x = w ~& y;
```

## Operators - Arithmetic
```
// +
c = a + b; // if a and b are both one bit and are both 1, then c will be zero because 1+1=10, it be not capture the carry bit
{c,s} = a + b; // if a = b = 1, then c will be 1 and s will be 0
y = w + x // w and x are 4 bit each and are 1111, then y will need to be 5 bits to capture the whole sum 11110
{c,s} = w + x; // w and x are 4 bits, c is 1 bit, s is 4 bits

// -
c = a - b; // it is actually a + (-b), b's 2 bit complement is used
y = w - x; / if w and x are 4 bits, y would need to be 5 bit

// *
y = w * x; // if w and x are 4 bits, y would need to be 8 bits

// / division is not fully synthesizable, some cases where it is synthesizable
y = w / x; // if divisor is 2^n, then its synthesizable, it is done by shifting bits

// % not synthesizable at all
y = w % x; // y will be the remainder
```

## Operators - Logical
```
// ==
c = (a == b); // c will be true or false, use xnor gate for this
c = (w == y); // w and y are 4 bit, c will also just be true or false

// !=
c = (a != b); // use xor gate for this
c = (w != y);

// === (only when you have x or z for a or b, not synthesizable)
a = 10z1;
b = 1x11;
c = (a === b); // c will be true because a and be will be taken as 10_1 and 1_11 (_ as dont care)

// !==
a = 10z1;
b = 1x11;
c = (a !== b); // c will be false

// AND (&&)
c = a && b; // a, b are 1 bit. If a and b is true, c is true
c = w && y; // w, y are 4 bit. If w and y are nonzero values, c is true. If either/both w and y are 0000, c is false.
// Pass w through an OR gate to see if any of the bits are 1. Then do that with y. Then put those 2 values into an AND gate.

// OR (||)
c = a || b; // a, b are 1 bit. If a or b is 1, c is true.
c = w || y; // w, y are 4 bit. If w or y is a nonzero num, c is true.
// Pass w through an OR gate. Pass y through an OR gate. Pass those 2 values through an OR gate.

// NOT (!)
c = !a;
c = !w; // If w is nonzero, c if false. If w is 0000, c is true.
```

## Operators - Relational
```
// >
c = a > b;
c = w > x;
/* if (w[3] > x[3]) {
     c is true
   } else if (w[3] == x[3]) {
       if (w[2] > x[2]) {
         c is true
       } else if ...
     } */

// <

// >=

// <=
```

## Operators - Reduction
```
// &
c = &w; // w is 4 bits, w[3] & w[2] & w[1] & w[0]. c is a 1 bit output

// |
c = |w; // w[3] | w[2] | w[1] | w[0]

// ^

// ~&

// ~|

// ~^
```

## Operators - Shift
```
// << logical left shift
y = w << 2; // w = 10101100, y = 10110000

// >> logical right shift
y = w >> 2; // w = 10101100, y = 00101011

// >>> arithmetic right shift (only used for signed nums), not all synthesis tools can synthesize
y = w >>> 2; // w = 11001010, num becomes 00110010 after logical shift, but the sign bit needs to be retained, so y = 11110010

// <<< arithmetic left shift (only for signed nums), no synthesis tools support this
y = w <<< 2; // w = 11001010, y = 00101000
```

## Operators - Concatenation
```
// { }
y = {w,x}; // w,x are 4 bit. y is 8 bit
y = {a,c,b};
y = {x,w[1:0],z[3:2]};
```

## Operators - Repetition
```
// {{}}
y = {4{a,b}}; // y = abababab
```

## Operators - Conditional
```
// ?
y = s ? x : z; // if s is true, y = x. if s is false, y = z. HW is 2 input mux. s is select
y = s ? a & b : a | b;
y = a > b ? a & b : a | b;
```

## Output Resolution Table
AND
b\a|0|1|x|z
---|-|-|-|-
 0 |0|0|0|0
 1 |0|1|x|x
 x |0|x|x|x
 z |0|x|x|x

OR
b\a|0|1|x|z
---|-|-|-|-
 0 |0|1|x|x
 1 |1|1|1|1
 x |x|1|x|x
 z |x|1|x|x

XOR
 b\a|0|1|x|z
---|-|-|-|-
 0 |0|1|x|x
 1 |1|0|x|x
 x |x|x|x|x
 z |x|x|x|x

NAND
 b\a|0|1|x|z
---|-|-|-|-
 0 |1|1|1|1
 1 |1|0|x|x
 x |1|x|x|x
 z |1|x|x|x

 NOR
 b\a|0|1|x|z
---|-|-|-|-
 0 |1|0|x|x
 1 |0|0|0|0
 x |x|0|x|x
 z |x|0|x|x

 XNOR
 b\a|0|1|x|z
---|-|-|-|-
 0 |1|0|x|x
 1 |0|1|x|x
 x |x|x|x|x
 z |x|x|x|x

 NOT
 Input|Output
:-:|:-:
 0|1
 1|0
 x|x
 z|x

 buf
 Input|Output
 :-:|:-:
 0|0
 1|1
 x|x
 z|x

## 4-bit Full Adder (Structural)

Put together 4 1-bit full adders

Ripple carry full adder:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dfbb84e5-fafa-41f7-905a-867319c031c1)

We cannot use dataflow or behavioral to connect blocks.

```
module full_adder_4bit_st(s,cout,a,b,cin);
 input [3:0] a, b;
 input cin;
 output [3:0]s;
 output cout;

 wire n1, n2, n3;

 full_adder_bh fa1(s[0],n1,a[0],b[0],cin);
 full_adder_bh fa2(s[1],n2,a[1],b[1],n1);
 full_adder_bh fa3(s[2],n3,a[2],b[2],n2);
 full_adder_bh fa4(s[3],cout,a[3],b[3],n3);
endmodule
```

## 4-bit Full Adder (Dataflow)
```
module full_adder_4bit_df(s,cout,a,b,cin);
 input [3:0]a,b;
 input cin;
 output [3:0]s;
 output cout;

 assign {cout,s} = a + b + cin;

endmodule
```

## 4-bit Full Adder (Behavioral)
```
module full_adde_4bit_bh(s,cout,a,b,cin);
 input [3:0]a,b;
 input cin;
 output reg [3:0]s;
 output reg cout;

 always @(a,b,cin)
     {cout,s} = a + b + cin;

endmodule
```

## 4-bit full adder test bench
```
module full_adder_4bit_bh_tb;
 // These need to be reg because they will be used on left side of the initial block
 reg [3:0]a,b;
 reg cin;

 wire [3:0]s;
 wire cout;

 full_adder_4bit_bh fa4_dut(s,cout,a,b,cin);

 initial
 $monitor("time=%d \t a=%b \t b=%b \t cin=%b \t s=%b \t cout=%b",
 $time,a,b,cin,s,cout);

 initial begin
  a = 0;
  a = 0;
  cin = 0;
  repeat(16) begin
   #10 a=a+1
   repeat(16) begin
    #10 b=b+1
    repeat(2)
     #10 cin=~cin
   end // repeat(16)
  end // repeat(16)
 end
endmodule
```

## 2 x 1 Multiplexer (Dataflow)
```
module mux_2_1_df(Y,I,S);
  input [1:0]I;
  input S;
  output Y;

  assign Y = S?I[1]:I[0];

endmodule
```

## 2 x 1 Mux (behavioral)
```
module mux_2_1_bh(Y,I,S);
 input [1:0]I;
 input S;
 output reg Y;

 // We don't need begin and end because we have only 1 if statement
 always @(*)
  if(S)
   Y = I[1];
  else
   Y = I[0];
endmodule
```

Use dataflow when you know the boolean expression. Use behavioral when you do not.

## 4 x 1 Mux (Dataflow 1)
```
module mux_4_1_df(Y,I,S);
 input [3:0]I;
 input [1:0]S;
 output Y;

 assign Y = I[S];
endmodule
```

## 4 x 1 Mux (Dataflow 2)
```
module mux_4_1_df(Y,I,S);
 input [3:0]I;
 input [1:0]S;
 output Y;

 assign Y = ~|S?I[0]:(&S?I[3]:(S[0]?I[1]:I[2]));

endmodule
```

## 4 x 1 Mux (Dataflow 3)
```
module mux_4_1_df(Y,I,S);
 input [3:0]I;
 input [1:0]S;
 output Y;

 assign Y = (S==2'd0)?I[0]:((S==2'd1)?I[1]:((S==2'd2)?I[2]:I[3]));

endmodule
```

## 4 x 1 Mux (Behavioral)
```
module mux_2_1_df(Y,I,S);
 input [3:0]I;
 input [3:0]S;
 output reg Y;

 always @(*)
  case (S)
   2'd0: Y=I[0];
   2'd1: Y=I[1];
   2'd2: Y=I[2];
   2'd3: Y=I[3];
   default:$display("error");  // ignored by synthesis tool
  endcase
endmodule
```

## 2 x 4 Decode (Dataflow)
```
module decode_2_4_df1(Y,I,En);
 input [1:0]I;
 input En;
 output [3:0]Y;

 assign Y = {En & I[1] & I[0],
             En & I[1] & ~I[0],
             En & ~I[1] & I[0],
             En & ~I[1] & ~I[0]};

endmodule
```

Dataflow will usually produce the design with the least/simplest hardware.

## 2 x 4 Decode (Behavioral)
```
module decode_2_4_bh(Y,I,En);
 input [1:0]I;
 input En;
 output [3:0]Y;

 always @(*) begin
  case({En,I})  // case statement generates a mux
   3'b100: Y=4'b0001;
   3'b101: Y=4'b0010;
   3'b110: Y=4'b0100;
   3'b111: Y=4'b1000;
   3'b000,
   3'b001,
   3'b010,
   3'b011: Y=4'b0001;
   default: $display("error");
  endcase
 end
endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/90a42847-2028-4101-b439-4ae898fdbc3f)

Depending on the synthesis tool, it may recognize that you are trying to make a decoder.

## 3 x 8 Decoder (Dataflow)
```
module decode_3_8_df2(Y,I,En);
 input [2:0]I;
 input En;
 output [7:0]Y;

 assign Y = {En & I[2] & I[1] & I[0],
             En & I[2] & I[1] & ~I[0],
             En & I[2] & ~I[1] & I[0],
             En & I[2] & ~I[1] & ~I[0],
             En & ~I[2] & I[1] & I[0],
             En & ~I[2] & I[1] & ~I[0],
             En & ~I[2] & ~I[1] & I[0],
             En & ~I[2] & ~I[1] & ~I[0]};
endmodule
```

## 4 x 2 Encoder (Dataflow)

One of the outputs is a valid bit. That bit is 0 when the input is 0000, which is not 1 out of the 4 valid inputs.
```
module encode_4_2_df(Y,V,I);
 input [3:0]I;
 output [1:0]Y;
 output V;

 assign Y = {I[3]|I[2], I[3]|I[1]);
 assign V = |I;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7a80b780-e1e4-44ea-9542-f63e228613b9)

## 4 x 2 Encoder (Behavioral)

```
module encode_4_2_bh(Y,V,I);
 input [3:0]I;
 output reg [1:0]Y;
 output reg V;

 always @(*) begin
  case (I)
   4'd1: {V,Y}=3'b100;
   4'd2: {V,Y}=3'b101;
   4'd4: {V,Y}=3'b110;
   4'd8: {V,Y}=3'b111;
   4'd0,4'd3,4'd5,4'd6,4'd7,4'd9,4'd10,
   4'd11,4'd12,4'd13,4'd14,4'd15: {V,Y}=3'b000;
   default: $display("error");
  endcase
 end
endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e3ca0150-9486-4c26-a661-cfacc53b775e)

## 4 x 2 Priority Encoder (Behavioral)

```
module encode_4_2_priority_bh(Y,V,I);
 input [3:0]I;
 output reg [1:0]Y;
 output reg V;

 always @(*) begin
  if (I[0]) {V,Y}=3'b100;
  else if (I[1]) {V,Y}=3'b101;
  else if (I[2]) {V,Y}=3'b110;
  else if (I[3]) {V,Y}=3'b111;
  else {V,Y}=3'b000;
 end
endmodule
```

Each if statement creates a mux:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ee31665-0eae-454c-a90e-e1d878c34f1b)

## 4 x 2 Priority Encoder (Dataflow)
```
module encode_4_2_priority_df(Y,V,I);
 input [3:0]I;
 output [1:0]Y;
 output V;

 assign {V,Y} = I[0]?3'b100:I[1]?3'b101:I[2]?3'b110:I[3]?3'b111:3'b000;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8db67dd4-14ee-4f76-aaa5-7ec824db2de2)

## 4-bit Comparator (Dataflow 1)
```
module comparator_df1(Ed,Gt,Sm,A,B);
 input [3:0]A,B;
 output Eq,Gt,Sm;

 assign Eq = &(A ~^ B); // A == B
 assign Gt = (A[3]& ~B[3]) | ((A[3]~^B[3]) & (A[2]& ~B[2])) |
             ((A[3]~^B[3]) & (A[2]~^B[2]) & (A[1]& ~B[1])) |
             ((A[3]~^B[3]) & (A[2]~^B[2]) & (A[1]~^B[1]) & (A[0]& ~B[0])); //A > B
 assign Sm = ~(Gt|Eq);

endmodule
```

## 4-bit Comparator (Dataflow 2)
```
module comparator_df2(Eq,Gt,Sm,A,B);
 input [3:0]A,B;
 output Eq,Gt,Sm;
 
 assign Eq= (A==B); // A==b
 assign Gt= (A>B); // A>B
 assign Sm= (A<B); // A<B

 // Call also write "assign {Eq,Gt,Sm} = {A==B,A>B,A<B};

endmodule
```

## 4-bit comparator (Behavioral)
```
module comparator_bh(Eq,Gt,Sm,A,B);
 input [3:0]A,B;
 output reg Eq,Gt,Sm;

 always @(*) begin
  Eq= (A==B);
  Gt= (A>B);
  Sm= (A<B);
 end

endmodule
```

## 8-bit Barrel Shifter (combinational left & right)
```
module barrel_bh(Out,In,Lr,n);
 input [7:0]In;
 input [2:0]n;
 input Lr;
 output reg [7:0]Out;

 always @(*) begin
  if(Lr)
   Out = In << n;
  else
   Out = In >> n;
 end

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/feb65af5-09ff-479c-bf4a-63b4e3f9ecd7)

Right shift is the same, but inputs and outputs are in reverse order.

## Designing Arithmetic & Logic Unit (ALU)
```
module ALU(x,y,a,b,opcode);
 input [3:0]a,b,opcode;
 output reg [3:0]x,y;

 always @(a,b,opcode)
  case (opcode)
   4'b0000: x[0] = |a;
   4'b0001: x[0] = &a;
   4'b0010: x[0] = ^a;
   4'b0011: x = a & b;
   4'b0100: x = a | b;
   4'b0101: x = a ^ b;
   4'b0110: x[0] = a > b;
   4'b0111: x[0] = a < b;
   4'b1000: x[0] = !a;
   4'b1001: x[0] = a==b;
   4'b1010: {y[0],x} = a+b;
   4'b1011: x = a-b;
   4'b1100: {y,x} = a*b;
   4'b1101: {y,x} = a>>b;
   4'b1110: {y,x} = a<<b;
   4'b1111: x = ~a;
   default: $display("error");
  endcase
endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/42d6a463-9df0-47de-9104-adb9e594095e)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c2770fb2-8f8a-40de-9faa-1bf82d34be09)
