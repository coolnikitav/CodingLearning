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
